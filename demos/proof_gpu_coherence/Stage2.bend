# proof_gpu_coherence -- stage 2 (OPTIONS-DESIGN.md §2-§3), a preview
# of a design not yet built. The device marks the chunks it writes in a
# map; the enter uploads the DIRTY chunks and makes them CLEAN and read
# only; the leave invalidates I, the marked chunks and every chunk from
# the ceiling (the chunk holding the enter's H_TWIN_HI) up to n, and
# prefetches P, the history's chunks in I or already STALE. The host
# side (accesses, faults, the lock) and the bump are main.bend's.
# Stage2Laws.bend states the laws, Stage2Proof.bend proves them.
import Base
import ./main.bend as M

# hic: the ceiling chunk; m: the store marks its chunk (a twin_mark)
type Ev is Data:
  Rd{c: Nat}
  Wr{c: Nat, v: Nat}
  Stp{c: Nat, k: M.K}
  Ent{key: Nat, hic: Nat}
  DWr{c: Nat, v: Nat, m: Bool}
  Bmp{m: Nat}
  Lv{}

# The enter: the map is zeroed (the leave's hipMemset); a DIRTY chunk
# goes up, then PROT_READ and CLEAN
def en2(ch: M.Ch) -> M.Ch:
  match ch:
    case M.Ch{st, pr, lk, pd, +h, d, g, hw, pf, used, mk}:
      match st:
        case M.Dy{}:
          M.Ch{M.Cl{}, M.PR{}, lk, pd, h, h, g, hw, pf, used, False{}}
        case M.Cl{}:
          M.Ch{M.Cl{}, pr, lk, pd, h, d, g, hw, pf, used, False{}}
        case M.Sl{}:
          M.Ch{M.Sl{}, pr, lk, pd, h, d, g, hw, pf, used, False{}}
        case M.Fe{}:
          M.Ch{M.Fe{}, pr, lk, pd, h, d, g, hw, pf, used, False{}}

def en2s(xs: List<&2, M.Ch>) -> List<&2, M.Ch>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      en2(h) <> en2s(t)

def Hs.tw(hs: M.Hs) -> Nat:
  match hs:
    case M.Hs{pfm, turns, gkey, keys, at, cur, writes, tw}:
      tw

def set_tw(+t: Nat, hs: M.Hs) -> M.Hs:
  match hs:
    case M.Hs{pfm, turns, gkey, keys, at, cur, writes, tw}:
      M.Hs{pfm, turns, gkey, keys, at, cur, writes, t}

# A device store of v into chunk c, marking it if m
def dw2(+v: Nat, m: Bool, ch: M.Ch) -> M.Ch:
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      M.Ch{st, pr, lk, pd, h, v, v, hw, pf, used, Bool.or(mk, m)}

def upd2(xs: List<&2, M.Ch>, c: Nat, +v: Nat, m: Bool) -> List<&2, M.Ch>:
  match xs c:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      dw2(v, m, h) <> t
    case h <> t 1n+p:
      h <> upd2(t, p, v, m)

# The leave, on a chunk under the ceiling: marked, it is in I (stage
# 1's leave: FETCHED if p, else STALE); unmarked, a STALE chunk is
# fetched if p, and any other stays as it is
def lv2.o(p: Bool, ch: M.Ch) -> M.Ch:
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match st:
        case M.Sl{}:
          M.lv1(p, M.Ch{M.Sl{}, pr, lk, pd, h, d, g, hw, pf, used, mk})
        case M.Dy{}:
          M.Ch{M.Dy{}, pr, lk, pd, h, d, g, hw, pf, used, mk}
        case M.Cl{}:
          M.Ch{M.Cl{}, pr, lk, pd, h, d, g, hw, pf, used, mk}
        case M.Fe{}:
          M.Ch{M.Fe{}, pr, lk, pd, h, d, g, hw, pf, used, mk}

def lv2h.go(mk: Bool, p: Bool, ch: M.Ch) -> M.Ch:
  match mk:
    case True{}:
      M.lv1(p, ch)
    case False{}:
      lv2.o(p, ch)

def Ch.mk(ch: M.Ch) -> Bool:
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      mk

def lv2h(p: Bool, +ch: M.Ch) -> M.Ch:
  lv2h.go(Ch.mk(ch), p, ch)

# t chunks under the ceiling, then the device extent (all of it in I)
def lv2s(t: Nat, xs: List<&2, M.Ch>, ps: List<&2, Bool>) -> List<&2, M.Ch>:
  match t:
    case 0n:
      M.lv1s(xs, ps)
    case 1n+u:
      match xs:
        case Nil{}:
          Nil{}
        case h <> r:
          match ps:
            case Nil{}:
              lv2h(False{}, h) <> lv2s(u, r, Nil{})
            case p <> q:
              lv2h(p, h) <> lv2s(u, r, q)

# P, what the leave copies down (for the counts): p, in I or STALE
def pe.st(st: M.St) -> Bool:
  match st:
    case M.Sl{}:
      True{}
    case M.Dy{}:
      False{}
    case M.Cl{}:
      False{}
    case M.Fe{}:
      False{}

def pe(i: Bool, p: Bool, +ch: M.Ch) -> Bool:
  Bool.and(p, Bool.or(Bool.or(i, Ch.mk(ch)), pe.st(M.Ch.st(ch))))

def pes(xs: List<&2, M.Ch>, ps: List<&2, Bool>, +t: Nat) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      Nil{}
    case +h <> r:
      match ps:
        case Nil{}:
          False{} <> pes(r, Nil{}, Nat.sub(t, 1n))
        case p <> q:
          pe(Nat.is_eq(t, 0n), p, h) <> pes(r, q, Nat.sub(t, 1n))

# t: the ceiling (gpu_fetch keeps it)
def lv.fin(ph: M.Ph, +ins: List<&2, M.Ch>, outs: List<&2, M.Ch>, +t: Nat, r: List<&2, Bool> & M.Hs) -> M.Sys:
  match r:
    case (+ps, hs):
      M.Sys{M.Host{}, lv2s(t, ins, ps), outs, M.lv_count(pes(ins, ps, t), hs)}

def step(s: M.Sys, e: Ev) -> M.Sys:
  match s:
    case M.Sys{ph, +ins, +outs, +hs}:
      match e:
        case Rd{c}:
          M.on(c, M.CRd{}, ph, ins, outs, hs)
        case Wr{c, v}:
          M.on(c, M.CWr{v}, ph, ins, outs, hs)
        case Stp{c, k}:
          M.on(c, M.CSt{k}, ph, ins, outs, hs)
        case DWr{c, v, m}:
          M.Sys{ph, upd2(ins, c, v, m), outs, hs}
        case Ent{k, t}:
          M.Sys{M.Dev{}, en2s(ins), outs, set_tw(t, M.hs_enter(k, M.nfetched(ins), hs))}
        case Bmp{+m}:
          M.Sys{ph, M.rs_in(ins, m, outs), M.rs_out(ins, m, outs), hs}
        case Lv{}:
          lv.fin(ph, ins, outs, Hs.tw(hs), M.lv_hs(M.len(ins), Nat.add(M.len(ins), M.len(outs)), hs))

def run(es: List<&2, Ev>, s: M.Sys) -> M.Sys:
  match es:
    case Nil{}:
      s
    case e <> t:
      run(t, step(s, e))

# Hypotheses
# ----------

# every device store under the ceiling marks its chunk: a store that
# does not mark lands at or above the ceiling
def MkOk(m: Bool, t: Nat, c: Nat) -> Type:
  match m:
    case True{}:
      Unit
    case False{}:
      M.LE(t, c)

def Hs.ok(hs: M.Hs, m: Bool, c: Nat) -> Type:
  match hs:
    case M.Hs{pfm, turns, gkey, keys, at, cur, writes, tw}:
      MkOk(m, tw, c)

# main.bend's, and: the ceiling is under n at the enter; a device store
# that does not mark is at or above the ceiling
def Ok(s: M.Sys, e: Ev) -> Type:
  match s:
    case M.Sys{ph, +ins, +outs, hs}:
      match e:
        case Rd{c}:
          M.IsHost(ph)
        case Wr{c, v}:
          M.IsHost(ph)
        case Stp{c, k}:
          M.IsHost(ph)
        case Ent{k, t}:
          (M.IsHost(ph) & (M.AllQ(ins) & M.LE(t, M.len(ins))))
        case DWr{+c, v, m}:
          (M.IsDev(ph) & (M.LE(1n+c, M.len(ins)) & Hs.ok(hs, m, c)))
        case Bmp{m}:
          M.BOk(ph, ins, m, outs)
        case Lv{}:
          M.IsDev(ph)

def Valid(es: List<&2, Ev>, s: M.Sys) -> Type:
  match es:
    case Nil{}:
      Unit
    case e <> t:
      (Ok(s, e) & Valid(t, step(s, e)))

# The laws' terms (and main.bend's L1-L4)
# ---------------------------------------

# K0: a chunk that is not STALE holds the device's bytes
def K0c(ch: M.Ch) -> Type:
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match st:
        case M.Sl{}:
          Unit
        case M.Dy{}:
          {h == d : Nat}
        case M.Cl{}:
          {h == d : Nat}
        case M.Fe{}:
          {h == d : Nat}

def AllK0(xs: List<&2, M.Ch>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case h <> t:
      (K0c(h) & AllK0(t))

def K0(s: M.Sys) -> Type:
  match s:
    case M.Sys{ph, ins, outs, hs}:
      AllK0(ins)

def RO(pr: M.Pr) -> Type:
  match pr:
    case M.PN{}:
      Empty
    case M.PR{}:
      Unit
    case M.PW{}:
      Empty

# an unmarked chunk the leave keeps: never DIRTY; CLEAN read only and
# FETCHED no access, each holding the device's bytes; STALE no access
def Coh.st(st: M.St, pr: M.Pr, h: Nat, d: Nat) -> Type:
  match st:
    case M.Dy{}:
      Empty
    case M.Cl{}:
      ({h == d : Nat} & RO(pr))
    case M.Sl{}:
      M.NoAcc(pr)
    case M.Fe{}:
      ({h == d : Nat} & M.NoAcc(pr))

def Coh(ch: M.Ch) -> Type:
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match mk:
        case True{}:
          Unit
        case False{}:
          Coh.st(st, pr, h, d)

def UCs(t: Nat, xs: List<&2, M.Ch>) -> Type:
  match t:
    case 0n:
      Unit
    case 1n+u:
      match xs:
        case Nil{}:
          Unit
        case h <> r:
          (Coh(h) & UCs(u, r))

# L5, in a turn: a chunk under the ceiling the device has not marked
# is one the leave may keep
def L5(s: M.Sys) -> Type:
  match s:
    case M.Sys{ph, ins, outs, hs}:
      match ph:
        case M.Host{}:
          Unit
        case M.Dev{}:
          UCs(Hs.tw(hs), ins)

# the device writes chunk 2 (the ceiling, unmarked) and chunk 0
# (marked); the leave (prefetch all) fetches both and keeps chunk 1
def main() -> List<&2, List<&2, Nat>>:
  M.shows(run([Wr{0n, 5n}, Ent{1n, 2n}, DWr{2n, 7n, False{}}, DWr{0n, 8n, True{}}, Lv{}], M.init(3n, 0n, 2n)))
