# proof_gpu_coherence -- the laws, over every trace from the start that
# Valid allows (main.bend's Ok, event by event: host accesses and fault
# steps only between turns; an enter with no thread in gpu_fault; a
# device store under n, in a turn; n only grows, and a turn's growth
# does not sweep in a chunk the host wrote above n). n0 chunks start
# under n and m0 above; pfm is BEND_GPU_PREFETCH. PROOF.bend proves
# them. They are about the model; the differential test outside the
# repo ties the model to the C on its traces, nothing here proves the C.
# Safety only: nothing here says a fault ever opens its chunk.
import Base
import ./main.bend as M

# L1: between turns, a chunk the host may read holds the last value
# written to it, by the host or the device
law l1_read_fresh:
  for +n0: Nat
  for +m0: Nat
  for +pfm: Nat
  for +es: List<&2, M.Ev>
  for v: M.Valid(es, M.init(n0, m0, pfm))
  M.L1(M.run(es, M.init(n0, m0, pfm)))

# L2: no lost write. Between turns a STALE chunk with no section open
# traps and the device holds its last write, so a download brings the
# last write and no host write lands meanwhile; a chunk the enter
# uploads is readable. In a turn every chunk under n holds its last
# write on the device: every host write went up at the enter, and a
# leave's prefetch copies the last write
law l2_no_lost_write:
  for +n0: Nat
  for +m0: Nat
  for +pfm: Nat
  for +es: List<&2, M.Ev>
  for v: M.Valid(es, M.init(n0, m0, pfm))
  M.L2(M.run(es, M.init(n0, m0, pfm)))

# L3: between turns, a FETCHED chunk with no section open traps, and
# its host (alias) bytes and device bytes are the last write
law l3_prefetch_current:
  for +n0: Nat
  for +m0: Nat
  for +pfm: Nat
  for +es: List<&2, M.Ev>
  for v: M.Valid(es, M.init(n0, m0, pfm))
  M.L3(M.run(es, M.init(n0, m0, pfm)))

# L4: a chunk the interval's leave fetched is still FETCHED or counted
# used exactly once; no other chunk is counted used
law l4_used_once:
  for +n0: Nat
  for +m0: Nat
  for +pfm: Nat
  for +es: List<&2, M.Ev>
  for v: M.Valid(es, M.init(n0, m0, pfm))
  M.L4(M.run(es, M.init(n0, m0, pfm)))
