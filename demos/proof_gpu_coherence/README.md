# GPU chunk coherence, proven

The HIP lane's lazy chunk protocol in `bend2/comp.ts` at 32c8d44e
(`gpu_fault`, `gpu_heap`'s enter and leave, `gpu_fetch`, `gpu_touch`,
`gpu_publish`), modelled, with its safety laws proven in Bend.

- `main.bend`: the model. Per chunk: state, host protection, host and
  device bytes, and a ghost holding the last write. Events at the C's
  atomicity: host read and write, each later step of a fault, enter,
  device store, leave and its prefetch, bump.
- `LAWS.bend`: the laws, for any event list the hypotheses allow.
- `Chunk.bend`, `PROOF.bend`: the invariant and its proof.

`bun bend2/main.ts demos/proof_gpu_coherence/PROOF.bend --check-only`

## Laws (safety only)

- L1: between turns, a chunk the host may read holds the last write.
- L2 no lost write: between turns, a STALE chunk with no section open
  traps and VRAM holds its last write, and a chunk the enter uploads is
  readable; in a turn, every chunk under n holds its last write in VRAM.
- L3: between turns, a FETCHED chunk with no section open traps, and
  its host bytes equal VRAM and the last write.
- L4: per chunk, FETCHED (0 or 1) plus used = the leave fetched it.

No liveness: a fault that never opens its chunk keeps them all.

## Hypotheses (`Ok` in main.bend)

- Host accesses and fault steps run between turns; an enter finds no
  thread in `gpu_fault` (comp.ts 5686-5690).
- Device stores land under n.
- n only grows: `heap_alloc` adds to H_BUMP before its capacity check
  and ERR_HEAP keeps the add, n clamps at gpu_hi, and the u32 is
  assumed never to wrap. A shrunken n breaks L1 and L2.
- A bump in a turn sweeps no chunk the host wrote above n (implied by
  "the host accesses only under its bump").
- Fresh bump memory is written before it is read, on both sides: the
  model starts every word at 0, the C zeroes VRAM only below STAK_OFF.

## Not modelled

Chunk runs and the GAP merge; the memfd layout; timing counters; the
device running beside the host (turns are exclusive); weak memory (the
model is sequentially consistent); a trap and its first state load as two
steps (merged: the diff test runs the C's late loads); `wr == 2`;
mprotect and hipMemcpy failures; `gpu_show`'s upload. The laws hold for
any prefetch set.

## Tested against the C

`logs/cohmodel` (outside the repo) runs the C's functions from
32c8d44e, one pthread per access, against the model: heap ends inside,
below and above [gpu_lo, gpu_hi], bumps in turns (VRAM header only),
served late loads. It compares the first, middle and last word of each
tracked chunk. Not compared: the header (only through n), [STAT_OFF,
gpu_lo), [gpu_hi, end), rings and banks (stubbed); dropping either
copy outside [gpu_lo, gpu_hi) goes unseen. Untested: a late load that
finds its chunk mid-section (argued harmless: it changes nothing
shared), and gpu_hi's round-down (gpu_hi sits on 4 MB).

## Stage 2 preview

`Stage2.bend` models OPTIONS-DESIGN.md §2-§3: the device marks what it
writes, the enter makes uploads CLEAN and read only, the leave
invalidates the marked chunks and those from the ceiling (the chunk of
the enter's `H_TWIN_HI`) up. `Stage2Laws.bend` states L1-L4, L5 (an
unmarked chunk under the ceiling may be kept) and K0 (after the
uploads, every chunk not STALE equals VRAM); `Stage2Proof.bend` proves
them, given that an unmarked device store lands at or above the
ceiling and the ceiling is under n.

For the stage-2 C: a kept FETCHED chunk's used/unused counts cross
keys (waste can pass 100%; record the fetch's owner or epoch); kept
CLEAN chunks leave the history (reads never fault, CLEAN writes skip
`gpu_cur`); the ceiling rounds down; uploads go read only (left DIRTY,
a write faults forever). The model covers strict marking only, not the
RET_H dead-slot exemptions or the two-extent allocator, and its states
are relative to gpu_lo: the C's map, by absolute chunk, must offset.
