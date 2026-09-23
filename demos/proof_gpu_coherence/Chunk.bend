# proof_gpu_coherence -- the invariant and its per-chunk lemmas: each
# chunk event, the device's write, and a chunk's enter and leave keep it.
import Base
import ./main.bend as M

# The invariant
# -------------

def IsR(pr: M.Pr) -> Type:
  match pr:
    case M.PN{}:
      Empty
    case M.PR{}:
      Unit
    case M.PW{}:
      Empty

def IsW(pr: M.Pr) -> Type:
  match pr:
    case M.PN{}:
      Empty
    case M.PR{}:
      Empty
    case M.PW{}:
      Unit

def Pos(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

# an opened section (SOp, FOp): a write fault opened read-write (h the
# last write, the device's may be older), a read fault read only
def HI.op(w: Bool, pr: M.Pr, h: Nat, d: Nat, g: Nat) -> Type:
  match w:
    case True{}:
      (IsW(pr) & {h == g : Nat})
    case False{}:
      (IsR(pr) & ({h == d : Nat} & {d == g : Nat}))

# CLEAN: read only with the device's bytes, or read-write while a
# thread between its mprotect and its exchange (ar) will make it dirty
def HI.cl(pr: M.Pr, ar: Nat, h: Nat, d: Nat, g: Nat) -> Type:
  match pr:
    case M.PN{}:
      Empty
    case M.PR{}:
      ({h == g : Nat} & ({h == d : Nat} & M.Z(ar)))
    case M.PW{}:
      ({h == g : Nat} & Pos(ar))

# STALE: no access, the device's bytes the last; copied: the alias too
def HI.sl(lk: M.Lk, pr: M.Pr, h: Nat, d: Nat, g: Nat) -> Type:
  match lk:
    case M.Free{}:
      (M.NoAcc(pr) & {d == g : Nat})
    case M.SCp{w}:
      (M.NoAcc(pr) & ({h == d : Nat} & {d == g : Nat}))
    case M.SOp{w}:
      HI.op(w, pr, h, d, g)
    case M.FOp{w}:
      Empty

# FETCHED: no access, host and device bytes the last
def HI.fe(lk: M.Lk, pr: M.Pr, h: Nat, d: Nat, g: Nat) -> Type:
  match lk:
    case M.Free{}:
      (M.NoAcc(pr) & ({h == d : Nat} & {d == g : Nat}))
    case M.SCp{w}:
      Empty
    case M.SOp{w}:
      Empty
    case M.FOp{w}:
      HI.op(w, pr, h, d, g)

# no thread on the lock-free CLEAN path
def NoCl(lc: Nat, ar: Nat) -> Type:
  (M.Z(lc) & M.Z(ar))

def HI.st(st: M.St, pr: M.Pr, lk: M.Lk, lc: Nat, ar: Nat, h: Nat, d: Nat, g: Nat) -> Type:
  match st:
    case M.Dy{}:
      (M.IsFree(lk) & (IsW(pr) & {h == g : Nat}))
    case M.Cl{}:
      (M.IsFree(lk) & HI.cl(pr, ar, h, d, g))
    case M.Sl{}:
      (NoCl(lc, ar) & HI.sl(lk, pr, h, d, g))
    case M.Fe{}:
      (NoCl(lc, ar) & HI.fe(lk, pr, h, d, g))

# a chunk under n between turns
def HI(ch: M.Ch) -> Type:
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match pd:
        case M.Pd{lc, ar, f0, f1, s0, s1}:
          HI.st(st, pr, lk, lc, ar, h, d, g)

def DI.b(ch: M.Ch) -> Type:
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      {d == g : Nat}

# a chunk under n in a turn: nobody in the handler, the device's bytes
# the last
def DI(+ch: M.Ch) -> Type:
  (M.Quiet(ch) & DI.b(ch))

def OI.hw(hw: Bool, d: Nat, g: Nat) -> Type:
  match hw:
    case True{}:
      Unit
    case False{}:
      {d == g : Nat}

def OI.b(ch: M.Ch) -> Type:
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match st:
        case M.Dy{}:
          (IsW(pr) & ({h == g : Nat} & OI.hw(hw, d, g)))
        case M.Cl{}:
          Empty
        case M.Sl{}:
          Empty
        case M.Fe{}:
          Empty

# a chunk above n: dirty, read-write, the host's the last; the device's
# too unless the host wrote it there
def OI(+ch: M.Ch) -> Type:
  (M.Quiet(ch) & OI.b(ch))

def CI(ph: M.Ph, +ch: M.Ch) -> Type:
  match ph:
    case M.Host{}:
      (M.L4c(ch) & HI(ch))
    case M.Dev{}:
      (M.L4c(ch) & DI(ch))

def CO(+ch: M.Ch) -> Type:
  (M.L4c(ch) & OI(ch))

def AI(+ph: M.Ph, xs: List<&2, M.Ch>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case h <> t:
      (CI(ph, h) & AI(ph, t))

def AO(xs: List<&2, M.Ch>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case h <> t:
      (CO(h) & AO(t))

def Inv(s: M.Sys) -> Type:
  match s:
    case M.Sys{+ph, ins, outs, hs}:
      (AI(ph, ins) & AO(outs))

# Host events on a chunk under n
# ------------------------------

def CH(+ch: M.Ch) -> Type:
  (M.L4c(ch) & HI(ch))

def fault_ok(wr: Bool, ch: M.Ch, i: CH(ch)) -> CH(M.fault(wr, ch)):
  match wr:
    case True{}:
      match ch:
        case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
          match st:
            case M.Dy{}:
              i
            case M.Cl{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  i
            case M.Sl{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  i
            case M.Fe{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  i
    case False{}:
      match ch:
        case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
          match st:
            case M.Dy{}:
              i
            case M.Cl{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  i
            case M.Sl{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  i
            case M.Fe{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  i

def tr(-a: Nat, -b: Nat, -c: Nat, ab: {a == b : Nat}, bc: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, ab, bc)

def read_ok(ch: M.Ch, i: CH(ch)) -> CH(M.read(ch)):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match pr:
        case M.PN{}:
          fault_ok(False{}, M.Ch{st, M.PN{}, lk, pd, h, d, g, hw, pf, used, mk}, i)
        case M.PR{}:
          i
        case M.PW{}:
          i

# an opened section written: still opened, the write the last
def op_w(w: Bool, -v: Nat, -h: Nat, -d: Nat, -g: Nat, x: HI.op(w, M.PW{}, h, d, g)) -> HI.op(w, M.PW{}, v, d, v):
  match w:
    case True{}:
      (Unit{}, {==})
    case False{}:
      match x:
        case (r, e):
          match r:

# a write that lands
def write_pw(o: Bool, +v: Nat, st: M.St, lk: M.Lk, pd: M.Pd, h: Nat, d: Nat, g: Nat, hw: Bool, pf: Bool, used: Nat, mk: Bool,
  i: CH(M.Ch{st, M.PW{}, lk, pd, h, d, g, hw, pf, used, mk}))
  -> CH(M.Ch{st, M.PW{}, lk, pd, v, d, v, Bool.or(o, hw), pf, used, mk}):
  match st:
    case M.Dy{}:
      match pd:
        case M.Pd{lc, ar, f0, f1, s0, s1}:
          match i:
            case (l4, hi):
              match hi:
                case (fr, x):
                  (l4, (fr, (Unit{}, {==})))
    case M.Cl{}:
      match pd:
        case M.Pd{lc, ar, f0, f1, s0, s1}:
          match i:
            case (l4, hi):
              match hi:
                case (fr, x):
                  match x:
                    case (e, p):
                      (l4, (fr, ({==}, p)))
    case M.Sl{}:
      match lk pd:
        case M.Free{} M.Pd{lc, ar, f0, f1, s0, s1}:
          match i:
            case (l4, hi):
              match hi:
                case (nc, x):
                  match x:
                    case (n, e):
                      match n:
        case M.SCp{w} M.Pd{lc, ar, f0, f1, s0, s1}:
          match i:
            case (l4, hi):
              match hi:
                case (nc, x):
                  match x:
                    case (n, e):
                      match n:
        case M.SOp{w} M.Pd{lc, ar, f0, f1, s0, s1}:
          match i:
            case (l4, hi):
              match hi:
                case (nc, x):
                  (l4, (nc, op_w(w, v, h, d, g, x)))
        case M.FOp{w} M.Pd{lc, ar, f0, f1, s0, s1}:
          match i:
            case (l4, hi):
              match hi:
                case (nc, x):
                  match x:
    case M.Fe{}:
      match lk pd:
        case M.Free{} M.Pd{lc, ar, f0, f1, s0, s1}:
          match i:
            case (l4, hi):
              match hi:
                case (nc, x):
                  match x:
                    case (n, e):
                      match n:
        case M.SCp{w} M.Pd{lc, ar, f0, f1, s0, s1}:
          match i:
            case (l4, hi):
              match hi:
                case (nc, x):
                  match x:
        case M.SOp{w} M.Pd{lc, ar, f0, f1, s0, s1}:
          match i:
            case (l4, hi):
              match hi:
                case (nc, x):
                  match x:
        case M.FOp{w} M.Pd{lc, ar, f0, f1, s0, s1}:
          match i:
            case (l4, hi):
              match hi:
                case (nc, x):
                  (l4, (nc, op_w(w, v, h, d, g, x)))

def write_ok(o: Bool, +v: Nat, ch: M.Ch, i: CH(ch)) -> CH(M.write(o, v, ch)):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match pr:
        case M.PN{}:
          fault_ok(True{}, M.Ch{st, M.PN{}, lk, pd, h, d, g, hw, pf, used, mk}, i)
        case M.PR{}:
          fault_ok(True{}, M.Ch{st, M.PR{}, lk, pd, h, d, g, hw, pf, used, mk}, i)
        case M.PW{}:
          write_pw(o, v, st, lk, pd, h, d, g, hw, pf, used, mk, i)

# lock-free CLEAN path: the mprotect opens only a clean or dirty chunk
def k_lc_ok(ch: M.Ch, i: CH(ch)) -> CH(M.k_lc(ch)):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match st:
        case M.Dy{}:
          match pd:
            case M.Pd{lc, ar, f0, f1, s0, s1}:
              match lc:
                case 0n:
                  i
                case 1n+p:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (fr, x):
                          match x:
                            case (w, e):
                              (l4, (fr, (Unit{}, e)))
        case M.Cl{}:
          match pr:
            case M.PN{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (fr, x):
                          match x:
            case M.PR{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match lc:
                    case 0n:
                      i
                    case 1n+p:
                      match i:
                        case (l4, hi):
                          match hi:
                            case (fr, x):
                              match x:
                                case (hg, y):
                                  (l4, (fr, (hg, Unit{})))
            case M.PW{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match lc:
                    case 0n:
                      i
                    case 1n+p:
                      match i:
                        case (l4, hi):
                          match hi:
                            case (fr, x):
                              match x:
                                case (hg, y):
                                  (l4, (fr, (hg, Unit{})))
        case M.Sl{}:
          match pd:
            case M.Pd{lc, ar, f0, f1, s0, s1}:
              match lc:
                case 0n:
                  i
                case 1n+p:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (nc, x):
                          match nc:
                            case (zl, za):
                              match zl:
        case M.Fe{}:
          match pd:
            case M.Pd{lc, ar, f0, f1, s0, s1}:
              match lc:
                case 0n:
                  i
                case 1n+p:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (nc, x):
                          match nc:
                            case (zl, za):
                              match zl:

# 2: the exchange finds the chunk clean (read-write) or dirty
def k_ar_ok(ch: M.Ch, i: CH(ch)) -> CH(M.k_ar(ch)):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match st:
        case M.Dy{}:
          match pd:
            case M.Pd{lc, ar, f0, f1, s0, s1}:
              match ar:
                case 0n:
                  i
                case 1n+p:
                  i
        case M.Cl{}:
          match pr:
            case M.PN{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (fr, x):
                          match x:
            case M.PR{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match ar:
                    case 0n:
                      i
                    case 1n+p:
                      match i:
                        case (l4, hi):
                          match hi:
                            case (fr, x):
                              match x:
                                case (hg, y):
                                  match y:
                                    case (hd, z):
                                      match z:
            case M.PW{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match ar:
                    case 0n:
                      i
                    case 1n+p:
                      match i:
                        case (l4, hi):
                          match hi:
                            case (fr, x):
                              match x:
                                case (hg, y):
                                  (l4, (fr, (Unit{}, hg)))
        case M.Sl{}:
          match pd:
            case M.Pd{lc, ar, f0, f1, s0, s1}:
              match ar:
                case 0n:
                  i
                case 1n+p:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (nc, x):
                          match nc:
                            case (zl, za):
                              match za:
        case M.Fe{}:
          match pd:
            case M.Pd{lc, ar, f0, f1, s0, s1}:
              match ar:
                case 0n:
                  i
                case 1n+p:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (nc, x):
                          match nc:
                            case (zl, za):
                              match za:

# under the lock, FETCHED read again: opened, still current
def kf_go_ok(wr: Bool, st: M.St, pr: M.Pr, lc: Nat, ar: Nat, f0: Nat, f1: Nat, s0: Nat, s1: Nat,
  h: Nat, d: Nat, g: Nat, hw: Bool, pf: Bool, used: Nat, mk: Bool,
  i: CH(M.Ch{st, pr, M.Free{}, M.Pd{lc, ar, f0, f1, s0, s1}, h, d, g, hw, pf, used, mk}))
  -> CH(M.kf.go(wr, st, pr, M.Free{}, M.Pd{lc, ar, f0, f1, s0, s1}, h, d, g, hw, pf, used, mk)):
  match wr:
    case True{}:
      match st:
        case M.Fe{}:
          match i:
            case (l4, hi):
              match hi:
                case (nc, x):
                  match x:
                    case (n, y):
                      match y:
                        case (hd, dg):
                          (l4, (nc, (Unit{}, tr(h, d, g, hd, dg))))
        case M.Dy{}:
          i
        case M.Cl{}:
          i
        case M.Sl{}:
          i
    case False{}:
      match st:
        case M.Fe{}:
          match i:
            case (l4, hi):
              match hi:
                case (nc, x):
                  match x:
                    case (n, y):
                      (l4, (nc, (Unit{}, y)))
        case M.Dy{}:
          i
        case M.Cl{}:
          i
        case M.Sl{}:
          i

# under the lock, STALE read again: copied into the alias, still trapping
def ks_go_ok(wr: Bool, st: M.St, pr: M.Pr, lc: Nat, ar: Nat, f0: Nat, f1: Nat, s0: Nat, s1: Nat,
  h: Nat, +d: Nat, g: Nat, hw: Bool, pf: Bool, used: Nat, mk: Bool,
  i: CH(M.Ch{st, pr, M.Free{}, M.Pd{lc, ar, f0, f1, s0, s1}, h, d, g, hw, pf, used, mk}))
  -> CH(M.ks.go(wr, st, pr, M.Free{}, M.Pd{lc, ar, f0, f1, s0, s1}, h, d, g, hw, pf, used, mk)):
  match st:
    case M.Sl{}:
      match i:
        case (l4, hi):
          match hi:
            case (nc, x):
              match x:
                case (n, dg):
                  (l4, (nc, (n, ({==}, dg))))
    case M.Dy{}:
      i
    case M.Cl{}:
      i
    case M.Fe{}:
      i

def k_f1_ok(ch: M.Ch, i: CH(ch)) -> CH(M.k_f1(ch)):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match lk:
        case M.Free{}:
          match pd:
            case M.Pd{lc, ar, f0, f1, s0, s1}:
              match f1:
                case 0n:
                  i
                case 1n+p:
                  kf_go_ok(True{}, st, pr, lc, ar, f0, p, s0, s1, h, d, g, hw, pf, used, mk, i)
        case M.SCp{w}:
          i
        case M.SOp{w}:
          i
        case M.FOp{w}:
          i

def k_f0_ok(ch: M.Ch, i: CH(ch)) -> CH(M.k_f0(ch)):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match lk:
        case M.Free{}:
          match pd:
            case M.Pd{lc, ar, f0, f1, s0, s1}:
              match f0:
                case 0n:
                  i
                case 1n+p:
                  kf_go_ok(False{}, st, pr, lc, ar, p, f1, s0, s1, h, d, g, hw, pf, used, mk, i)
        case M.SCp{w}:
          i
        case M.SOp{w}:
          i
        case M.FOp{w}:
          i

def k_s1_ok(ch: M.Ch, i: CH(ch)) -> CH(M.k_s1(ch)):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match lk:
        case M.Free{}:
          match pd:
            case M.Pd{lc, ar, f0, f1, s0, s1}:
              match s1:
                case 0n:
                  i
                case 1n+p:
                  ks_go_ok(True{}, st, pr, lc, ar, f0, f1, s0, p, h, d, g, hw, pf, used, mk, i)
        case M.SCp{w}:
          i
        case M.SOp{w}:
          i
        case M.FOp{w}:
          i

def k_s0_ok(ch: M.Ch, i: CH(ch)) -> CH(M.k_s0(ch)):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match lk:
        case M.Free{}:
          match pd:
            case M.Pd{lc, ar, f0, f1, s0, s1}:
              match s0:
                case 0n:
                  i
                case 1n+p:
                  ks_go_ok(False{}, st, pr, lc, ar, f0, f1, p, s1, h, d, g, hw, pf, used, mk, i)
        case M.SCp{w}:
          i
        case M.SOp{w}:
          i
        case M.FOp{w}:
          i

# an opened section's store: the state it opened for
def op_st(wr: Bool, pr: M.Pr, lc: Nat, ar: Nat, h: Nat, d: Nat, g: Nat, nc: NoCl(lc, ar), x: HI.op(wr, pr, h, d, g))
  -> HI.st(M.open_st(wr), pr, M.Free{}, lc, ar, h, d, g):
  match wr:
    case True{}:
      (Unit{}, x)
    case False{}:
      match pr:
        case M.PN{}:
          match x:
            case (r, y):
              match r:
        case M.PR{}:
          match nc:
            case (zl, za):
              match x:
                case (r, y):
                  match y:
                    case (+hd, dg):
                      (Unit{}, (tr(h, d, g, hd, dg), (hd, za)))
        case M.PW{}:
          match x:
            case (r, y):
              match r:

# an opened state is not FETCHED
def l4_open(wr: Bool, -u: Nat, -pf: Bool, l4: {u == M.b2n(pf) : Nat}) -> {Nat.add(M.b2n(M.is_f(M.open_st(wr))), u) == M.b2n(pf) : Nat}:
  match wr:
    case True{}:
      l4
    case False{}:
      l4

# a copied chunk's mprotect: opened for the fault
def op_pr(wr: Bool, h: Nat, d: Nat, g: Nat, hd: {h == d : Nat}, dg: {d == g : Nat}) -> HI.op(wr, M.open_pr(wr), h, d, g):
  match wr:
    case True{}:
      (Unit{}, tr(h, d, g, hd, dg))
    case False{}:
      (Unit{}, (hd, dg))

def k_lk_ok(ch: M.Ch, i: CH(ch)) -> CH(M.k_lk(ch)):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match st:
        case M.Dy{}:
          match lk:
            case M.Free{}:
              i
            case M.SCp{wr}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (fr, x):
                          match fr:
            case M.SOp{wr}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (fr, x):
                          match fr:
            case M.FOp{wr}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (fr, x):
                          match fr:
        case M.Cl{}:
          match lk:
            case M.Free{}:
              i
            case M.SCp{wr}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (fr, x):
                          match fr:
            case M.SOp{wr}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (fr, x):
                          match fr:
            case M.FOp{wr}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (fr, x):
                          match fr:
        case M.Sl{}:
          match lk:
            case M.Free{}:
              i
            case M.SCp{+wr}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (nc, x):
                          match x:
                            case (n, y):
                              match y:
                                case (hd, dg):
                                  (l4, (nc, op_pr(wr, h, d, g, hd, dg)))
            case M.SOp{+wr}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (nc, x):
                          (l4_open(wr, used, pf, l4), op_st(wr, pr, lc, ar, h, d, g, nc, x))
            case M.FOp{wr}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (nc, x):
                          match x:
        case M.Fe{}:
          match lk:
            case M.Free{}:
              i
            case M.SCp{wr}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (nc, x):
                          match x:
            case M.SOp{wr}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (nc, x):
                          match x:
            case M.FOp{+wr}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (nc, x):
                          (l4_open(wr, 1n+used, pf, l4), op_st(wr, pr, lc, ar, h, d, g, nc, x))

def kstep_ok(k: M.K, ch: M.Ch, i: CH(ch)) -> CH(M.kstep(k, ch)):
  match k:
    case M.KLC{}:
      k_lc_ok(ch, i)
    case M.KAR{}:
      k_ar_ok(ch, i)
    case M.KF{wr}:
      match wr:
        case True{}:
          k_f1_ok(ch, i)
        case False{}:
          k_f0_ok(ch, i)
    case M.KS{wr}:
      match wr:
        case True{}:
          k_s1_ok(ch, i)
        case False{}:
          k_s0_ok(ch, i)
    case M.KLk{}:
      k_lk_ok(ch, i)

# In a turn, the enter, the leave
# -------------------------------

def CD(+ch: M.Ch) -> Type:
  (M.L4c(ch) & DI(ch))

# a device store: the last write
def dwrite_ok(+v: Nat, ch: M.Ch, i: CD(ch)) -> CD(M.dwrite(v, ch)):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match pd:
        case M.Pd{lc, ar, f0, f1, s0, s1}:
          match i:
            case (l4, x):
              match x:
                case (q, e):
                  (l4, (q, {==}))

def sym(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

# the enter: with no thread in the handler, every chunk under n holds
# the last write on the device (a dirty one is uploaded)
def en1_ok(ch: M.Ch, q: M.Quiet(ch), i: CH(ch)) -> CD(M.en1(ch)):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match st:
        case M.Dy{}:
          match pd:
            case M.Pd{lc, ar, f0, f1, s0, s1}:
              match i:
                case (l4, hi):
                  match hi:
                    case (fr, x):
                      match x:
                        case (w, hg):
                          (l4, (q, hg))
        case M.Cl{}:
          match pr:
            case M.PN{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (fr, x):
                          match x:
            case M.PR{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (fr, x):
                          match x:
                            case (hg, y):
                              match y:
                                case (hd, z):
                                  (l4, (q, tr(d, h, g, sym(h, d, hd), hg)))
            case M.PW{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match ar:
                    case 0n:
                      match i:
                        case (l4, hi):
                          match hi:
                            case (fr, x):
                              match x:
                                case (hg, p):
                                  match p:
                    case 1n+a:
                      match q:
                        case (fr, zs):
                          match zs:
                            case (zl, zs2):
                              match zs2:
                                case (za, zr):
                                  match za:
        case M.Sl{}:
          match lk:
            case M.Free{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (nc, x):
                          match x:
                            case (n, dg):
                              (l4, (q, dg))
            case M.SCp{w}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match q:
                    case (fr, zs):
                      match fr:
            case M.SOp{w}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match q:
                    case (fr, zs):
                      match fr:
            case M.FOp{w}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match q:
                    case (fr, zs):
                      match fr:
        case M.Fe{}:
          match lk:
            case M.Free{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (nc, x):
                          match x:
                            case (n, y):
                              match y:
                                case (hd, dg):
                                  (l4, (q, dg))
            case M.SCp{w}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match q:
                    case (fr, zs):
                      match fr:
            case M.SOp{w}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match q:
                    case (fr, zs):
                      match fr:
            case M.FOp{w}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match q:
                    case (fr, zs):
                      match fr:

# the leave: stale, or fetched with the device's bytes; either traps
def lv1_ok(p: Bool, ch: M.Ch, i: CD(ch)) -> CH(M.lv1(p, ch)):
  match p:
    case True{}:
      match ch:
        case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
          match lk:
            case M.Free{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, x):
                      match x:
                        case (q, dg):
                          match q:
                            case (fr, zs):
                              match zs:
                                case (zl, zs2):
                                  match zs2:
                                    case (za, zr):
                                      ({==}, ((zl, za), (Unit{}, ({==}, dg))))
            case M.SCp{w}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, x):
                      match x:
                        case (q, dg):
                          match q:
                            case (fr, zs):
                              match fr:
            case M.SOp{w}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, x):
                      match x:
                        case (q, dg):
                          match q:
                            case (fr, zs):
                              match fr:
            case M.FOp{w}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, x):
                      match x:
                        case (q, dg):
                          match q:
                            case (fr, zs):
                              match fr:
    case False{}:
      match ch:
        case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
          match lk:
            case M.Free{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, x):
                      match x:
                        case (q, dg):
                          match q:
                            case (fr, zs):
                              match zs:
                                case (zl, zs2):
                                  match zs2:
                                    case (za, zr):
                                      ({==}, ((zl, za), (Unit{}, dg)))
            case M.SCp{w}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, x):
                      match x:
                        case (q, dg):
                          match q:
                            case (fr, zs):
                              match fr:
            case M.SOp{w}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, x):
                      match x:
                        case (q, dg):
                          match q:
                            case (fr, zs):
                              match fr:
            case M.FOp{w}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, x):
                      match x:
                        case (q, dg):
                          match q:
                            case (fr, zs):
                              match fr:
