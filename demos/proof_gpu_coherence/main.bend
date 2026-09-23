# proof_gpu_coherence: a model of the HIP lane's lazy chunk protocol
# (bend2/comp.ts: gpu_fault, gpu_heap, gpu_fetch, gpu_touch,
# gpu_publish), at the atomicity the C has. LAWS.bend states what it
# guarantees, PROOF.bend proves it; Stage2*.bend do the same for the
# write-map leave of OPTIONS-DESIGN.md §2-§3.
#
# A chunk's bytes are one Nat: h the host's (gpu_alias maps the same
# pages, so the alias holds h too), d the device's, g the last value
# anyone wrote (a ghost, the laws' reference). A host thread in
# gpu_fault is a count by where it stands (Pd), and the lock's
# sections, split where a raw access can run between their stores,
# are a stage a chunk (Lk). Chunks under n (the bump's chunk count) are
# ins, the rest outs: n is length(ins), and a bump moves the boundary.
import Base

# A chunk
# -------

type St is Data:
  Dy{}
  Cl{}
  Sl{}
  Fe{}

# the host mapping: none, read, read-write
type Pr is Data:
  PN{}
  PR{}
  PW{}

# a chunk's lock section (the C's gpu_lock[c]): a stale chunk copied
# into the alias (SCp), then opened (SOp); a fetched chunk opened
# (FOp); each before its state store. wr: the fault was a write
type Lk is Data:
  Free{}
  SCp{wr: Bool}
  SOp{wr: Bool}
  FOp{wr: Bool}

# threads in gpu_fault: lc loaded CLEAN on a write, before its
# mprotect; ar after it, before the exchange; f0, f1 (a read, a write)
# loaded FETCHED and s0, s1 STALE, before the lock
type Pd is Data:
  Pd{lc: Nat, ar: Nat, f0: Nat, f1: Nat, s0: Nat, s1: Nat}

# hw: the host wrote it while above n (ghost); pf: fetched at this
# interval's leave; used: its first touches counted used since; mk:
# the device marked it this turn (stage 2)
type Ch is Data:
  Ch{st: St, pr: Pr, lk: Lk, pd: Pd, h: Nat, d: Nat, g: Nat, hw: Bool, pf: Bool, used: Nat, mk: Bool}

def pd0() -> Pd:
  Pd{0n, 0n, 0n, 0n, 0n, 0n}

def ch0() -> Ch:
  Ch{Dy{}, PW{}, Free{}, pd0(), 0n, 0n, 0n, False{}, False{}, 0n, False{}}

def pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

# the fault's first load: the branch it takes, as a thread waiting
def pd_f(wr: Bool, pd: Pd) -> Pd:
  match wr pd:
    case True{} Pd{lc, ar, f0, f1, s0, s1}:
      Pd{lc, ar, f0, 1n+f1, s0, s1}
    case False{} Pd{lc, ar, f0, f1, s0, s1}:
      Pd{lc, ar, 1n+f0, f1, s0, s1}

def pd_s(wr: Bool, pd: Pd) -> Pd:
  match wr pd:
    case True{} Pd{lc, ar, f0, f1, s0, s1}:
      Pd{lc, ar, f0, f1, s0, 1n+s1}
    case False{} Pd{lc, ar, f0, f1, s0, s1}:
      Pd{lc, ar, f0, f1, 1n+s0, s1}

def pd_c(wr: Bool, pd: Pd) -> Pd:
  match wr pd:
    case True{} Pd{lc, ar, f0, f1, s0, s1}:
      Pd{1n+lc, ar, f0, f1, s0, s1}
    case False{} Pd{lc, ar, f0, f1, s0, s1}:
      Pd{lc, ar, f0, f1, s0, s1}

# gpu_fault's load: CLEAN and a write takes the lock-free path; FETCHED
# and STALE go for the lock; anything else was served already
def fault(wr: Bool, ch: Ch) -> Ch:
  match ch:
    case Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match st:
        case Dy{}:
          Ch{Dy{}, pr, lk, pd, h, d, g, hw, pf, used, mk}
        case Cl{}:
          Ch{Cl{}, pr, lk, pd_c(wr, pd), h, d, g, hw, pf, used, mk}
        case Sl{}:
          Ch{Sl{}, pr, lk, pd_s(wr, pd), h, d, g, hw, pf, used, mk}
        case Fe{}:
          Ch{Fe{}, pr, lk, pd_f(wr, pd), h, d, g, hw, pf, used, mk}

# a host read: done if the mapping allows it, else a fault
def read(ch: Ch) -> Ch:
  match ch:
    case Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match pr:
        case PN{}:
          fault(False{}, Ch{st, PN{}, lk, pd, h, d, g, hw, pf, used, mk})
        case PR{}:
          Ch{st, PR{}, lk, pd, h, d, g, hw, pf, used, mk}
        case PW{}:
          Ch{st, PW{}, lk, pd, h, d, g, hw, pf, used, mk}

# a host write of v: lands if read-write (it is the last write), else a
# fault. o: the chunk is above n (hw records it)
def write(o: Bool, +v: Nat, ch: Ch) -> Ch:
  match ch:
    case Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match pr:
        case PN{}:
          fault(True{}, Ch{st, PN{}, lk, pd, h, d, g, hw, pf, used, mk})
        case PR{}:
          fault(True{}, Ch{st, PR{}, lk, pd, h, d, g, hw, pf, used, mk})
        case PW{}:
          Ch{st, PW{}, lk, pd, v, d, v, Bool.or(o, hw), pf, used, mk}

# The fault's later steps
# -----------------------

# lock-free CLEAN path, 1: mprotect read-write, whatever the state now
def k_lc(ch: Ch) -> Ch:
  match ch:
    case Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match pd:
        case Pd{lc, ar, f0, f1, s0, s1}:
          match lc:
            case 0n:
              Ch{st, pr, lk, Pd{0n, ar, f0, f1, s0, s1}, h, d, g, hw, pf, used, mk}
            case 1n+p:
              Ch{st, PW{}, lk, Pd{p, 1n+ar, f0, f1, s0, s1}, h, d, g, hw, pf, used, mk}

# 2: exchange the state to DIRTY
def k_ar(ch: Ch) -> Ch:
  match ch:
    case Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match pd:
        case Pd{lc, ar, f0, f1, s0, s1}:
          match ar:
            case 0n:
              Ch{st, pr, lk, Pd{lc, 0n, f0, f1, s0, s1}, h, d, g, hw, pf, used, mk}
            case 1n+p:
              Ch{Dy{}, pr, lk, Pd{lc, p, f0, f1, s0, s1}, h, d, g, hw, pf, used, mk}

def open_pr(wr: Bool) -> Pr:
  match wr:
    case True{}:
      PW{}
    case False{}:
      PR{}

def open_st(wr: Bool) -> St:
  match wr:
    case True{}:
      Dy{}
    case False{}:
      Cl{}

# under the lock, the state read again: still FETCHED, mprotect; else
# nothing to do
def kf.go(+wr: Bool, st: St, pr: Pr, lk: Lk, pd: Pd, h: Nat, d: Nat, g: Nat, hw: Bool, pf: Bool, used: Nat, mk: Bool) -> Ch:
  match st:
    case Fe{}:
      Ch{Fe{}, open_pr(wr), FOp{wr}, pd, h, d, g, hw, pf, used, mk}
    case Dy{}:
      Ch{Dy{}, pr, lk, pd, h, d, g, hw, pf, used, mk}
    case Cl{}:
      Ch{Cl{}, pr, lk, pd, h, d, g, hw, pf, used, mk}
    case Sl{}:
      Ch{Sl{}, pr, lk, pd, h, d, g, hw, pf, used, mk}

# under the lock, the state read again: still STALE, download into the
# alias while it traps
def ks.go(+wr: Bool, st: St, pr: Pr, lk: Lk, pd: Pd, h: Nat, +d: Nat, g: Nat, hw: Bool, pf: Bool, used: Nat, mk: Bool) -> Ch:
  match st:
    case Sl{}:
      Ch{Sl{}, pr, SCp{wr}, pd, d, d, g, hw, pf, used, mk}
    case Dy{}:
      Ch{Dy{}, pr, lk, pd, h, d, g, hw, pf, used, mk}
    case Cl{}:
      Ch{Cl{}, pr, lk, pd, h, d, g, hw, pf, used, mk}
    case Fe{}:
      Ch{Fe{}, pr, lk, pd, h, d, g, hw, pf, used, mk}

# a thread that loaded FETCHED (a write if w) takes the lock: only
# when no section is open on the chunk (the lock is held through it)
def k_f1(ch: Ch) -> Ch:
  match ch:
    case Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match lk pd:
        case Free{} Pd{lc, ar, f0, f1, s0, s1}:
          match f1:
            case 0n:
              Ch{st, pr, Free{}, Pd{lc, ar, f0, 0n, s0, s1}, h, d, g, hw, pf, used, mk}
            case 1n+p:
              kf.go(True{}, st, pr, Free{}, Pd{lc, ar, f0, p, s0, s1}, h, d, g, hw, pf, used, mk)
        case SCp{w} pd:
          Ch{st, pr, SCp{w}, pd, h, d, g, hw, pf, used, mk}
        case SOp{w} pd:
          Ch{st, pr, SOp{w}, pd, h, d, g, hw, pf, used, mk}
        case FOp{w} pd:
          Ch{st, pr, FOp{w}, pd, h, d, g, hw, pf, used, mk}

def k_f0(ch: Ch) -> Ch:
  match ch:
    case Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match lk pd:
        case Free{} Pd{lc, ar, f0, f1, s0, s1}:
          match f0:
            case 0n:
              Ch{st, pr, Free{}, Pd{lc, ar, 0n, f1, s0, s1}, h, d, g, hw, pf, used, mk}
            case 1n+p:
              kf.go(False{}, st, pr, Free{}, Pd{lc, ar, p, f1, s0, s1}, h, d, g, hw, pf, used, mk)
        case SCp{w} pd:
          Ch{st, pr, SCp{w}, pd, h, d, g, hw, pf, used, mk}
        case SOp{w} pd:
          Ch{st, pr, SOp{w}, pd, h, d, g, hw, pf, used, mk}
        case FOp{w} pd:
          Ch{st, pr, FOp{w}, pd, h, d, g, hw, pf, used, mk}

def k_s1(ch: Ch) -> Ch:
  match ch:
    case Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match lk pd:
        case Free{} Pd{lc, ar, f0, f1, s0, s1}:
          match s1:
            case 0n:
              Ch{st, pr, Free{}, Pd{lc, ar, f0, f1, s0, 0n}, h, d, g, hw, pf, used, mk}
            case 1n+p:
              ks.go(True{}, st, pr, Free{}, Pd{lc, ar, f0, f1, s0, p}, h, d, g, hw, pf, used, mk)
        case SCp{w} pd:
          Ch{st, pr, SCp{w}, pd, h, d, g, hw, pf, used, mk}
        case SOp{w} pd:
          Ch{st, pr, SOp{w}, pd, h, d, g, hw, pf, used, mk}
        case FOp{w} pd:
          Ch{st, pr, FOp{w}, pd, h, d, g, hw, pf, used, mk}

def k_s0(ch: Ch) -> Ch:
  match ch:
    case Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match lk pd:
        case Free{} Pd{lc, ar, f0, f1, s0, s1}:
          match s0:
            case 0n:
              Ch{st, pr, Free{}, Pd{lc, ar, f0, f1, 0n, s1}, h, d, g, hw, pf, used, mk}
            case 1n+p:
              ks.go(False{}, st, pr, Free{}, Pd{lc, ar, f0, f1, p, s1}, h, d, g, hw, pf, used, mk)
        case SCp{w} pd:
          Ch{st, pr, SCp{w}, pd, h, d, g, hw, pf, used, mk}
        case SOp{w} pd:
          Ch{st, pr, SOp{w}, pd, h, d, g, hw, pf, used, mk}
        case FOp{w} pd:
          Ch{st, pr, FOp{w}, pd, h, d, g, hw, pf, used, mk}

# the open section's next store: a copied chunk is mprotected; an
# opened one takes its state (a fetched one counts used), and unlocks
def k_lk(ch: Ch) -> Ch:
  match ch:
    case Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match lk:
        case Free{}:
          Ch{st, pr, Free{}, pd, h, d, g, hw, pf, used, mk}
        case SCp{+wr}:
          Ch{st, open_pr(wr), SOp{wr}, pd, h, d, g, hw, pf, used, mk}
        case SOp{+wr}:
          Ch{open_st(wr), pr, Free{}, pd, h, d, g, hw, pf, used, mk}
        case FOp{+wr}:
          Ch{open_st(wr), pr, Free{}, pd, h, d, g, hw, pf, 1n+used, mk}

# which thread steps
type K is Data:
  KLC{}
  KAR{}
  KF{wr: Bool}
  KS{wr: Bool}
  KLk{}

def kstep(k: K, ch: Ch) -> Ch:
  match k:
    case KLC{}:
      k_lc(ch)
    case KAR{}:
      k_ar(ch)
    case KF{wr}:
      match wr:
        case True{}:
          k_f1(ch)
        case False{}:
          k_f0(ch)
    case KS{wr}:
      match wr:
        case True{}:
          k_s1(ch)
        case False{}:
          k_s0(ch)
    case KLk{}:
      k_lk(ch)

# a device store of v
def dwrite(+v: Nat, ch: Ch) -> Ch:
  match ch:
    case Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      Ch{st, pr, lk, pd, h, v, v, hw, pf, used, mk}

# an event on one chunk
type CE is Data:
  CRd{}
  CWr{v: Nat}
  CSt{k: K}
  CDw{v: Nat}

# o: the chunk is above n
def cev(o: Bool, e: CE, ch: Ch) -> Ch:
  match e:
    case CRd{}:
      read(ch)
    case CWr{v}:
      write(o, v, ch)
    case CSt{k}:
      kstep(k, ch)
    case CDw{v}:
      dwrite(v, ch)

# chunk c of ins, then of outs (c - length(ins))
def upd_i(xs: List<&2, Ch>, c: Nat, +e: CE) -> List<&2, Ch>:
  match xs c:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      cev(False{}, e, h) <> t
    case h <> t 1n+p:
      h <> upd_i(t, p, e)

def upd_at(xs: List<&2, Ch>, c: Nat, +e: CE) -> List<&2, Ch>:
  match xs c:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      cev(True{}, e, h) <> t
    case h <> t 1n+p:
      h <> upd_at(t, p, e)

def upd_o(n: Nat, c: Nat, +e: CE, xs: List<&2, Ch>) -> List<&2, Ch>:
  match n c:
    case 0n c:
      upd_at(xs, c, e)
    case 1n+m 0n:
      xs
    case 1n+m 1n+p:
      upd_o(m, p, e, xs)

# The enter, the leave, the bump
# ------------------------------

# stage 1 uploads the DIRTY chunks
def up1(st: St) -> Bool:
  match st:
    case Dy{}:
      True{}
    case Cl{}:
      False{}
    case Sl{}:
      False{}
    case Fe{}:
      False{}

def en1.go(u: Bool, st: St, pr: Pr, lk: Lk, pd: Pd, +h: Nat, d: Nat, g: Nat, hw: Bool, pf: Bool, used: Nat, mk: Bool) -> Ch:
  match u:
    case True{}:
      Ch{st, pr, lk, pd, h, h, g, hw, pf, used, mk}
    case False{}:
      Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}

def en1(ch: Ch) -> Ch:
  match ch:
    case Ch{+st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      en1.go(up1(st), st, pr, lk, pd, h, d, g, hw, pf, used, mk)

def en1s(xs: List<&2, Ch>) -> List<&2, Ch>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      en1(h) <> en1s(t)

# stage 1's leave: stale and no access; then, if p, a copy into the
# alias, fetched. pf and used start the interval
def lv1(p: Bool, ch: Ch) -> Ch:
  match p:
    case True{}:
      match ch:
        case Ch{st, pr, lk, pd, h, +d, g, hw, pf, used, mk}:
          Ch{Fe{}, PN{}, lk, pd, d, d, g, hw, True{}, 0n, mk}
    case False{}:
      match ch:
        case Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
          Ch{Sl{}, PN{}, lk, pd, h, d, g, hw, False{}, 0n, mk}

def lv1s(xs: List<&2, Ch>, ps: List<&2, Bool>) -> List<&2, Ch>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      match ps:
        case Nil{}:
          lv1(False{}, h) <> lv1s(t, Nil{})
        case p <> q:
          lv1(p, h) <> lv1s(t, q)

# n := m: the first m chunks of ins ++ outs are ins
def rs_in(ins: List<&2, Ch>, m: Nat, outs: List<&2, Ch>) -> List<&2, Ch>:
  match ins:
    case Nil{}:
      List.take(&2, Ch, outs, m)
    case h <> t:
      match m:
        case 0n:
          Nil{}
        case 1n+p:
          h <> rs_in(t, p, outs)

def rs_out(ins: List<&2, Ch>, m: Nat, outs: List<&2, Ch>) -> List<&2, Ch>:
  match ins:
    case Nil{}:
      List.drop(&2, Ch, outs, m)
    case h <> t:
      match m:
        case 0n:
          h <> List.append(&2, Ch, t, outs)
        case 1n+p:
          rs_out(t, p, outs)

# History and counts
# ------------------

# a GpuKey slot: live (hist != NULL), its key, last leave, history and
# counts
type Gk is Data:
  Gk{live: Bool, key: Nat, last: Nat, hist: List<&2, Bool>, demand: Nat, hits: Nat, used: Nat, unused: Nat, chunks: Nat, runs: Nat}

# gpu_pf, gpu_turns, gpu_key, gpu_keys, gpu_at (a slot), gpu_cur,
# gpu_writes; tw, stage 2's H_TWIN_HI as a chunk (the one holding it)
type Hs is Data:
  Hs{pfm: Nat, turns: Nat, gkey: Nat, keys: List<&2, Gk>, at: Maybe<&2, Nat>, cur: List<&2, Bool>, writes: Nat, tw: Nat}

type Ph is Data:
  Host{}
  Dev{}

type Sys is Data:
  Sys{ph: Ph, ins: List<&2, Ch>, outs: List<&2, Ch>, hs: Hs}

def zeros(n: Nat) -> List<&2, Bool>:
  List.replicate(Bool, n, False{})

def key0(+nc: Nat) -> Gk:
  Gk{False{}, 0n, 0n, zeros(nc), 0n, 0n, 0n, 0n, 0n, 0n}

def bit(+c: Nat, bs: List<&2, Bool>) -> Bool:
  Maybe.default(&2, Bool, List.get(&2, Bool, bs, c), False{})

def setbit(+c: Nat, bs: List<&2, Bool>) -> List<&2, Bool>:
  List.set(&2, Bool, bs, c, True{})

def is_f(st: St) -> Bool:
  match st:
    case Fe{}:
      True{}
    case Dy{}:
      False{}
    case Cl{}:
      False{}
    case Sl{}:
      False{}

def b2n(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def Ch.st(ch: Ch) -> St:
  match ch:
    case Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      st

def nfetched(xs: List<&2, Ch>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      Nat.add(b2n(is_f(Ch.st(h))), nfetched(t))

# what a chunk event tells gpu_touch and gpu_writes
type Sg is Data:
  SgNone{}
  SgUsed{}
  SgDemand{}
  SgWrite{}

def sg.lk(lk: Lk) -> Sg:
  match lk:
    case Free{}:
      SgNone{}
    case SCp{w}:
      SgNone{}
    case SOp{w}:
      SgDemand{}
    case FOp{w}:
      SgUsed{}

def sg.ar(ar: Nat, st: St) -> Sg:
  match ar:
    case 0n:
      SgNone{}
    case 1n+p:
      match st:
        case Cl{}:
          SgWrite{}
        case Dy{}:
          SgNone{}
        case Sl{}:
          SgNone{}
        case Fe{}:
          SgNone{}

def Ch.lk(ch: Ch) -> Lk:
  match ch:
    case Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      lk

def Ch.ar(ch: Ch) -> Nat:
  match ch:
    case Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match pd:
        case Pd{lc, ar, f0, f1, s0, s1}:
          ar

def sg.k(k: K, +ch: Ch) -> Sg:
  match k:
    case KLk{}:
      sg.lk(Ch.lk(ch))
    case KAR{}:
      sg.ar(Ch.ar(ch), Ch.st(ch))
    case KLC{}:
      SgNone{}
    case KF{w}:
      SgNone{}
    case KS{w}:
      SgNone{}

def sg(e: CE, m: Maybe<&2, Ch>) -> Sg:
  match e m:
    case e None{}:
      SgNone{}
    case CSt{k} Some{ch}:
      sg.k(k, ch)
    case CRd{} Some{ch}:
      SgNone{}
    case CWr{v} Some{ch}:
      SgNone{}
    case CDw{v} Some{ch}:
      SgNone{}

def key_touch(used: Bool, +c: Nat, k: Gk) -> Gk:
  match used:
    case True{}:
      match k:
        case Gk{live, key, last, hist, demand, hits, u, unused, chunks, runs}:
          Gk{live, key, last, hist, demand, hits, 1n+u, unused, chunks, runs}
    case False{}:
      match k:
        case Gk{live, key, last, +hist, demand, hits, u, unused, chunks, runs}:
          Gk{live, key, last, hist, 1n+demand, Nat.add(hits, b2n(bit(c, hist))), u, unused, chunks, runs}

def keys_at(+i: Nat, keys: List<&2, Gk>) -> Gk:
  Maybe.default(&2, Gk, List.get(&2, Gk, keys, i), key0(0n))

# gpu_touch: the chunk into gpu_cur, the count into gpu_at's key
def touch(used: Bool, +c: Nat, hs: Hs) -> Hs:
  match hs:
    case Hs{pfm, turns, gkey, +keys, at, cur, writes, tw}:
      match at:
        case None{}:
          Hs{pfm, turns, gkey, keys, None{}, cur, writes, tw}
        case Some{+i}:
          Hs{pfm, turns, gkey, List.set(&2, Gk, keys, i, key_touch(used, c, keys_at(i, keys))), Some{i}, setbit(c, cur), writes, tw}

def hs_sg(+c: Nat, s: Sg, hs: Hs) -> Hs:
  match s:
    case SgNone{}:
      hs
    case SgUsed{}:
      touch(True{}, c, hs)
    case SgDemand{}:
      touch(False{}, c, hs)
    case SgWrite{}:
      match hs:
        case Hs{pfm, turns, gkey, keys, at, cur, writes, tw}:
          Hs{pfm, turns, gkey, keys, at, cur, 1n+writes, tw}

def pub_key(+nf: Nat, cur: List<&2, Bool>, k: Gk) -> Gk:
  match k:
    case Gk{live, key, last, hist, demand, hits, used, unused, chunks, runs}:
      Gk{live, key, last, cur, demand, hits, used, Nat.add(unused, nf), chunks, runs}

# gpu_publish, at an enter: gpu_cur is the history of gpu_at's key
def publish(+nf: Nat, hs: Hs) -> Hs:
  match hs:
    case Hs{pfm, turns, gkey, +keys, at, +cur, writes, tw}:
      match at:
        case None{}:
          Hs{pfm, turns, gkey, keys, None{}, cur, writes, tw}
        case Some{+i}:
          Hs{pfm, turns, gkey, List.set(&2, Gk, keys, i, pub_key(nf, cur, keys_at(i, keys))),
            Some{i}, zeros(List.length(&2, Bool, cur)), writes, tw}

def hs_enter(+k: Nat, +nf: Nat, hs: Hs) -> Hs:
  match hs:
    case Hs{pfm, turns, gkey, keys, at, cur, writes, tw}:
      publish(nf, Hs{pfm, 1n+turns, k, keys, at, cur, writes, tw})

def Gk.live(k: Gk) -> Bool:
  match k:
    case Gk{live, key, last, hist, demand, hits, used, unused, chunks, runs}:
      live

def Gk.key(k: Gk) -> Nat:
  match k:
    case Gk{live, key, last, hist, demand, hits, used, unused, chunks, runs}:
      key

def Gk.last(k: Gk) -> Nat:
  match k:
    case Gk{live, key, last, hist, demand, hits, used, unused, chunks, runs}:
      last

def Gk.hist(k: Gk) -> List<&2, Bool>:
  match k:
    case Gk{live, key, last, hist, demand, hits, used, unused, chunks, runs}:
      hist

def slot.hit(hit: Bool, i: Nat, rest: Nat) -> Nat:
  match hit:
    case True{}:
      i
    case False{}:
      rest

# gpu_fetch's slot: the gkey's live slot, else the least recently left
# (the first of the least)
def slot.go(ks: List<&2, Gk>, +g: Nat, +i: Nat, +best: Nat, +bl: Nat) -> Nat:
  match ks:
    case Nil{}:
      best
    case +k <> t:
      slot.hit(Bool.and(Gk.live(k), Nat.is_eq(Gk.key(k), g)), i,
        slot.go(t, g, 1n+i, pick(Nat, Nat.is_lt(Gk.last(k), bl), i, best), pick(Nat, Nat.is_lt(Gk.last(k), bl), Gk.last(k), bl)))

def slot(+g: Nat, ks: List<&2, Gk>) -> Nat:
  match ks:
    case Nil{}:
      0n
    case +k <> t:
      slot.go(k <> t, g, 0n, 0n, Gk.last(k))

# a new key takes the slot empty
def claim.go(same: Bool, +g: Nat, +turns: Nat, +nc: Nat, k: Gk) -> Gk:
  match same:
    case True{}:
      match k:
        case Gk{live, key, last, hist, demand, hits, used, unused, chunks, runs}:
          Gk{live, key, turns, hist, demand, hits, used, unused, chunks, runs}
    case False{}:
      Gk{True{}, g, turns, zeros(nc), 0n, 0n, 0n, 0n, 0n, 0n}

def claim(+g: Nat, +turns: Nat, +nc: Nat, +k: Gk) -> Gk:
  claim.go(Bool.and(Gk.live(k), Nat.is_eq(Gk.key(k), g)), g, turns, nc, k)

# the prefetch set under n: none (gpu_pf 0), all (2), else the history
def pset.go(m: Nat, +n: Nat, hist: List<&2, Bool>) -> List<&2, Bool>:
  match m:
    case 0n:
      zeros(n)
    case 1n+p:
      match p:
        case 0n:
          List.take(&2, Bool, hist, n)
        case 1n+q:
          match q:
            case 0n:
              List.replicate(Bool, n, True{})
            case 1n+r:
              List.take(&2, Bool, hist, n)

def count(bs: List<&2, Bool>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case b <> t:
      Nat.add(b2n(b), count(t))

# maximal runs of fetched chunks: one hipMemcpy each
def runs.go(bs: List<&2, Bool>, prev: Bool) -> Nat:
  match bs:
    case Nil{}:
      0n
    case +b <> t:
      Nat.add(b2n(Bool.and(b, Bool.not(prev))), runs.go(t, b))

def nruns(bs: List<&2, Bool>) -> Nat:
  runs.go(bs, False{})

def fetched(+ps: List<&2, Bool>, k: Gk) -> Gk:
  match k:
    case Gk{live, key, last, hist, demand, hits, used, unused, chunks, runs}:
      Gk{live, key, last, hist, demand, hits, used, unused, Nat.add(chunks, count(ps)), Nat.add(runs, nruns(ps))}

# gpu_fetch: the slot (gpu_at), its prefetch set under n (P)
def lv_hs(+n: Nat, +nc: Nat, hs: Hs) -> List<&2, Bool> & Hs:
  match hs:
    case Hs{+pfm, +turns, +gkey, +keys, at, cur, writes, tw}:
      +i = slot(gkey, keys)
      +k = claim(gkey, turns, nc, keys_at(i, keys))
      (pset.go(pfm, n, Gk.hist(k)), Hs{pfm, turns, gkey, List.set(&2, Gk, keys, i, k), Some{i}, cur, writes, tw})

# and the chunks it fetched, in runs
def lv_count(+ps: List<&2, Bool>, hs: Hs) -> Hs:
  match hs:
    case Hs{pfm, turns, gkey, +keys, at, cur, writes, tw}:
      match at:
        case None{}:
          Hs{pfm, turns, gkey, keys, None{}, cur, writes, tw}
        case Some{+i}:
          Hs{pfm, turns, gkey, List.set(&2, Gk, keys, i, fetched(ps, keys_at(i, keys))), Some{i}, cur, writes, tw}

def len(xs: List<&2, Ch>) -> Nat:
  List.length(&2, Ch, xs)

# The system
# ----------

type Ev is Data:
  Rd{c: Nat}
  Wr{c: Nat, v: Nat}
  Stp{c: Nat, k: K}
  Ent{key: Nat}
  DWr{c: Nat, v: Nat}
  Bmp{m: Nat}
  Lv{}

def chunk(+c: Nat, +ins: List<&2, Ch>, outs: List<&2, Ch>) -> Maybe<&2, Ch>:
  List.get(&2, Ch, List.append(&2, Ch, ins, outs), c)

def on(+c: Nat, +e: CE, ph: Ph, +ins: List<&2, Ch>, +outs: List<&2, Ch>, hs: Hs) -> Sys:
  Sys{ph, upd_i(ins, c, e), upd_o(len(ins), c, e, outs), hs_sg(c, sg(e, chunk(c, ins, outs)), hs)}

def lv.fin(ph: Ph, ins: List<&2, Ch>, outs: List<&2, Ch>, r: List<&2, Bool> & Hs) -> Sys:
  match r:
    case (+ps, hs):
      Sys{Host{}, lv1s(ins, ps), outs, lv_count(ps, hs)}

def step(s: Sys, e: Ev) -> Sys:
  match s:
    case Sys{ph, +ins, +outs, +hs}:
      match e:
        case Rd{c}:
          on(c, CRd{}, ph, ins, outs, hs)
        case Wr{c, v}:
          on(c, CWr{v}, ph, ins, outs, hs)
        case Stp{c, k}:
          on(c, CSt{k}, ph, ins, outs, hs)
        case DWr{c, v}:
          on(c, CDw{v}, ph, ins, outs, hs)
        case Ent{k}:
          Sys{Dev{}, en1s(ins), outs, hs_enter(k, nfetched(ins), hs)}
        case Bmp{+m}:
          Sys{ph, rs_in(ins, m, outs), rs_out(ins, m, outs), hs}
        case Lv{}:
          lv.fin(ph, ins, outs, lv_hs(len(ins), Nat.add(len(ins), len(outs)), hs))

def run(es: List<&2, Ev>, s: Sys) -> Sys:
  match es:
    case Nil{}:
      s
    case e <> t:
      run(t, step(s, e))

# n0 chunks under n, m0 above; gpu_pf
def init(+n0: Nat, +m0: Nat, +pfm: Nat) -> Sys:
  +nc = Nat.add(n0, m0)
  Sys{Host{}, List.replicate(Ch, n0, ch0()), List.replicate(Ch, m0, ch0()),
    Hs{pfm, 0n, 0n, List.replicate(Gk, 8n, key0(nc)), None{}, zeros(nc), 0n, 0n}}

# Hypotheses
# ----------

def Z(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

def LE(a: Nat, b: Nat) -> Type:
  match a b:
    case 0n _:
      Unit
    case 1n+p 0n:
      Empty
    case 1n+p 1n+q:
      LE(p, q)

def IsHost(ph: Ph) -> Type:
  match ph:
    case Host{}:
      Unit
    case Dev{}:
      Empty

def IsDev(ph: Ph) -> Type:
  match ph:
    case Host{}:
      Empty
    case Dev{}:
      Unit

def IsFree(lk: Lk) -> Type:
  match lk:
    case Free{}:
      Unit
    case SCp{w}:
      Empty
    case SOp{w}:
      Empty
    case FOp{w}:
      Empty

# no thread in gpu_fault on the chunk, no section open
def Quiet(ch: Ch) -> Type:
  match ch:
    case Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match pd:
        case Pd{lc, ar, f0, f1, s0, s1}:
          (IsFree(lk) & (Z(lc) & (Z(ar) & (Z(f0) & (Z(f1) & (Z(s0) & Z(s1)))))))

def AllQ(xs: List<&2, Ch>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case h <> t:
      (Quiet(h) & AllQ(t))

def NoHw(ch: Ch) -> Type:
  match ch:
    case Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match hw:
        case True{}:
          Empty
        case False{}:
          Unit

# during a turn, the chunks a bump sweeps under n were not written by
# the host above n (the enter did not send them). "The host accesses
# only under n" implies it (hw stays false); this weaker form lets the
# laws cover a host write above n too (the stage-1 harness's t_clip)
def Swept(ph: Ph, m: Nat, xs: List<&2, Ch>) -> Type:
  match ph:
    case Host{}:
      Unit
    case Dev{}:
      match m xs:
        case 0n _:
          Unit
        case 1n+p Nil{}:
          Unit
        case 1n+p h <> t:
          (NoHw(h) & Swept(Dev{}, p, t))

# n only grows: m >= length(ins), and the sweep is clean. In the C, n
# is H_BUMP's end rounded up to a chunk and clamped to [gpu_lo, gpu_hi];
# H_BUMP only grows: heap_alloc adds to it before its capacity check
# and a failure (ERR_HEAP) does not undo it, which keeps it growing,
# and n clamps at gpu_hi. It holds unless the u32 H_BUMP wraps (2^32
# pages reserved, failures included), which the model assumes never
# happens
def BOk(ph: Ph, ins: List<&2, Ch>, m: Nat, outs: List<&2, Ch>) -> Type:
  match ins:
    case Nil{}:
      Swept(ph, m, outs)
    case h <> t:
      match m:
        case 0n:
          Empty
        case 1n+p:
          BOk(ph, t, p, outs)

# what each event needs: host accesses and fault steps between turns
# (no host thread runs in a turn, the enter or the leave); an enter
# with no thread in gpu_fault (the contract at comp.ts 5686-5690; above
# n none can be, those chunks never trap); a device store under n, in
# a turn; n monotone.
# Storage: every chunk starts with 0 on both sides, the value no one
# wrote. The C zeroes VRAM only below STAK_OFF, and a bump sweeps in
# storage never uploaded, so "the last write" means the last write to
# a word written at all: the laws say nothing of a word read before
# any side wrote it. That fresh bump memory is written before it is
# read, on the host and on the device, is the runtime's obligation,
# not checked here
def Ok(s: Sys, e: Ev) -> Type:
  match s:
    case Sys{ph, +ins, +outs, hs}:
      match e:
        case Rd{c}:
          IsHost(ph)
        case Wr{c, v}:
          IsHost(ph)
        case Stp{c, k}:
          IsHost(ph)
        case Ent{k}:
          (IsHost(ph) & AllQ(ins))
        case DWr{c, v}:
          (IsDev(ph) & LE(1n+c, len(ins)))
        case Bmp{m}:
          BOk(ph, ins, m, outs)
        case Lv{}:
          IsDev(ph)

def Valid(es: List<&2, Ev>, s: Sys) -> Type:
  match es:
    case Nil{}:
      Unit
    case e <> t:
      (Ok(s, e) & Valid(t, step(s, e)))

# The laws' terms
# ---------------

def NoAcc(pr: Pr) -> Type:
  match pr:
    case PN{}:
      Unit
    case PR{}:
      Empty
    case PW{}:
      Empty

def Rdable(pr: Pr) -> Type:
  match pr:
    case PN{}:
      Empty
    case PR{}:
      Unit
    case PW{}:
      Unit

# L1: a chunk the host may read holds the last write
def L1c(ch: Ch) -> Type:
  match ch:
    case Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match pr:
        case PN{}:
          Unit
        case PR{}:
          {h == g : Nat}
        case PW{}:
          {h == g : Nat}

def L2s(st: St, lk: Lk, pr: Pr, d: Nat, g: Nat) -> Type:
  match st:
    case Sl{}:
      match lk:
        case Free{}:
          (NoAcc(pr) & {d == g : Nat})
        case SCp{w}:
          Unit
        case SOp{w}:
          Unit
        case FOp{w}:
          Unit
    case Dy{}:
      Unit
    case Cl{}:
      Unit
    case Fe{}:
      Unit

def L2u(u: Bool, pr: Pr) -> Type:
  match u:
    case True{}:
      Rdable(pr)
    case False{}:
      Unit

# L2, between turns: a STALE chunk with no section open traps and the
# device holds its last write (what a fault downloads); a chunk the
# enter uploads is readable (the upload reads the host mapping)
def L2h(ch: Ch) -> Type:
  match ch:
    case Ch{+st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      (L2s(st, lk, pr, d, g) & L2u(up1(st), pr))

# L2, in a turn: every chunk under n holds the last write on the device
# (every host write went up at the enter; what a leave downloads)
def L2d(ch: Ch) -> Type:
  match ch:
    case Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      {d == g : Nat}

def L3s(st: St, lk: Lk, pr: Pr, h: Nat, d: Nat, g: Nat) -> Type:
  match st:
    case Fe{}:
      match lk:
        case Free{}:
          (NoAcc(pr) & ({h == d : Nat} & {d == g : Nat}))
        case SCp{w}:
          Unit
        case SOp{w}:
          Unit
        case FOp{w}:
          Unit
    case Dy{}:
      Unit
    case Cl{}:
      Unit
    case Sl{}:
      Unit

# L3: a FETCHED chunk with no section open traps, and host (alias) and
# device bytes are the last write
def L3c(ch: Ch) -> Type:
  match ch:
    case Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      L3s(st, lk, pr, h, d, g)

# L4: a chunk fetched at the interval's leave is FETCHED (unused) or
# was counted used once; any other chunk is neither
def L4c(ch: Ch) -> Type:
  match ch:
    case Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      {Nat.add(b2n(is_f(st)), used) == b2n(pf) : Nat}

type Law is Data:
  KL1{}
  KL2h{}
  KL2d{}
  KL3{}
  KL4{}

def Holds(l: Law, ch: Ch) -> Type:
  match l:
    case KL1{}:
      L1c(ch)
    case KL2h{}:
      L2h(ch)
    case KL2d{}:
      L2d(ch)
    case KL3{}:
      L3c(ch)
    case KL4{}:
      L4c(ch)

def All(+l: Law, xs: List<&2, Ch>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case h <> t:
      (Holds(l, h) & All(l, t))

def L1(s: Sys) -> Type:
  match s:
    case Sys{ph, ins, outs, hs}:
      match ph:
        case Host{}:
          (All(KL1{}, ins) & All(KL1{}, outs))
        case Dev{}:
          Unit

def L2(s: Sys) -> Type:
  match s:
    case Sys{ph, ins, outs, hs}:
      match ph:
        case Host{}:
          All(KL2h{}, ins)
        case Dev{}:
          All(KL2d{}, ins)

def L3(s: Sys) -> Type:
  match s:
    case Sys{ph, ins, outs, hs}:
      match ph:
        case Host{}:
          All(KL3{}, ins)
        case Dev{}:
          Unit

def L4(s: Sys) -> Type:
  match s:
    case Sys{ph, ins, outs, hs}:
      (All(KL4{}, ins) & All(KL4{}, outs))

# a chunk's state, protection and bytes, for main
def show(ch: Ch) -> List<&2, Nat>:
  match ch:
    case Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      [b2n(is_f(st)), h, d, g, used]

def shows.go(xs: List<&2, Ch>) -> List<&2, List<&2, Nat>>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      show(h) <> shows.go(t)

def shows(s: Sys) -> List<&2, List<&2, Nat>>:
  match s:
    case Sys{ph, ins, outs, hs}:
      shows.go(List.append(&2, Ch, ins, outs))

# the device writes chunk 0; its leave prefetches nothing (a cold key);
# a read downloads it; the next leave of key 1 prefetches it
def main() -> List<&2, List<&2, Nat>>:
  shows(run([Ent{1n}, DWr{0n, 7n}, Lv{}, Rd{0n}, Stp{0n, KS{False{}}}, Stp{0n, KLk{}}, Stp{0n, KLk{}}, Rd{0n},
    Ent{1n}, DWr{0n, 9n}, Lv{}], init(2n, 1n, 1n)))
