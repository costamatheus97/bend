# GPU chunk coherence, proven

A model of the HIP lane's lazy chunk protocol in `bend2/comp.ts` (as of
32c8d44e: `gpu_fault`, `gpu_heap`'s enter and leave, `gpu_fetch`,
`gpu_touch`, `gpu_publish`), with its safety laws proven in Bend.

- `main.bend`: the model. Per chunk: state (DIRTY, CLEAN, STALE,
  FETCHED), host protection, host bytes (the alias maps the same pages),
  device bytes, and a ghost holding the last value anyone wrote. Events
  come at the C's atomicity: host read and write; a fault's later steps
  as separate events (the lock-free CLEAN path's mprotect, then its
  exchange; the locked STALE copy, mprotect, store; the locked FETCHED
  recheck, mprotect, store); enter; device store; leave with its
  history-driven prefetch; bump of n.
- `LAWS.bend`: the laws, for any event list the hypotheses allow.
- `Chunk.bend`, `PROOF.bend`: the invariant, its preservation by every
  event, and the laws read off it.

Check:

```sh
bun bend2/main.ts demos/proof_gpu_coherence/PROOF.bend --check-only
```

## Laws

- L1 read freshness: between turns, a chunk the host may read holds the
  last value anyone wrote.
- L2 no lost write: between turns, a STALE chunk with no lock section
  open traps and the device holds its last write, and a chunk the enter
  uploads is readable; in a turn, every chunk under n holds its last
  write on the device.
- L3 prefetch integrity: between turns, a FETCHED chunk with no section
  open traps and its host bytes equal the device's and the last write.
- L4 used once: per chunk, FETCHED (0 or 1) plus its used count equals
  whether this interval's leave fetched it.

## Hypotheses (`Ok` in main.bend)

- Host accesses and fault steps run only between turns, and an enter
  finds no thread inside `gpu_fault` (comp.ts 5566-5572).
- The device stores only under n.
- n only grows. Without it a chunk the device wrote, then left above a
  shrunken n, keeps an old prefetch that a read opens (L1), and a host
  write left above n misses the upload (L2): the residual risk the C
  documents.
- A bump in a turn sweeps no chunk the host wrote while it was above n.

The laws hold for any prefetch set, so they do not depend on the
history. Not modelled: chunk runs and the GAP merge (upload per chunk),
the memfd layout, the zero-fill region, the counters' timing fields,
real concurrency of the device with the host (turns are exclusive).

## Stage 2 preview

`Stage2.bend` models OPTIONS-DESIGN.md §2-§3 before it is built: the
device marks what it writes, the enter makes uploads CLEAN and read
only, and the leave invalidates only the marked chunks and those from
the ceiling (the chunk holding the enter's `H_TWIN_HI`) up.
`Stage2Laws.bend` states L1-L4 again, plus L5 (an unmarked chunk under
the ceiling is one the leave may keep) and K0 (right after the
uploads, every chunk that is not STALE equals VRAM);
`Stage2Proof.bend` proves them. Its extra hypotheses: a device store
that does not mark lands at or above the ceiling, and the ceiling is
under n at the enter. L4 holds per fetch: a FETCHED chunk the leave
keeps is counted unused again at the next enter.
