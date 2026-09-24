# proof_gpu_coherence -- stage 2's laws (Stage2.bend), over every trace
# from the start that its Valid allows: main.bend's hypotheses, and
# every device store under the ceiling chunk marks its chunk, and the
# ceiling is under n at the enter. L1-L4 read as in LAWS.bend; L4 is
# per fetch (a FETCHED chunk the leave keeps keeps its count).
# Stage2Proof.bend proves them.
import Base
import ./main.bend as M
import ./Stage2.bend as S

law s2_l1_read_fresh:
  for +n0: Nat
  for +m0: Nat
  for +pfm: Nat
  for +es: List<&2, S.Ev>
  for v: S.Valid(es, M.init(n0, m0, pfm))
  M.L1(S.run(es, M.init(n0, m0, pfm)))

law s2_l2_no_lost_write:
  for +n0: Nat
  for +m0: Nat
  for +pfm: Nat
  for +es: List<&2, S.Ev>
  for v: S.Valid(es, M.init(n0, m0, pfm))
  M.L2(S.run(es, M.init(n0, m0, pfm)))

law s2_l3_prefetch_current:
  for +n0: Nat
  for +m0: Nat
  for +pfm: Nat
  for +es: List<&2, S.Ev>
  for v: S.Valid(es, M.init(n0, m0, pfm))
  M.L3(S.run(es, M.init(n0, m0, pfm)))

law s2_l4_used_once:
  for +n0: Nat
  for +m0: Nat
  for +pfm: Nat
  for +es: List<&2, S.Ev>
  for v: S.Valid(es, M.init(n0, m0, pfm))
  M.L4(S.run(es, M.init(n0, m0, pfm)))

# L5: in a turn, every unmarked chunk under the ceiling is one the
# leave may keep (not DIRTY; CLEAN read only or FETCHED with the last
# write; STALE trapping): the design's "not invalidating is sound"
law s2_l5_unmarked_keepable:
  for +n0: Nat
  for +m0: Nat
  for +pfm: Nat
  for +es: List<&2, S.Ev>
  for v: S.Valid(es, M.init(n0, m0, pfm))
  S.L5(S.run(es, M.init(n0, m0, pfm)))

# K0: right after an enter's uploads, every chunk under n that is not
# STALE holds the device's bytes
law s2_k0_enter:
  for +n0: Nat
  for +m0: Nat
  for +pfm: Nat
  for +es: List<&2, S.Ev>
  for v: S.Valid(es, M.init(n0, m0, pfm))
  for +k: Nat
  for +t: Nat
  for ok: S.Ok(S.run(es, M.init(n0, m0, pfm)), S.Ent{k, t})
  S.K0(S.step(S.run(es, M.init(n0, m0, pfm)), S.Ent{k, t}))
