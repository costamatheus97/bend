# proof_gpu_coherence -- the proofs of LAWS.bend. Inv holds at init,
# every event Ok allows keeps it, and each law is read off Inv.
# Chunk.bend has Inv and the per-chunk lemmas.
import Base
import ./main.bend as M
import ./Chunk.bend as Ck
import ./LAWS.bend as Laws

# Chunks above n
# --------------

# a host event on a chunk
def HostCE(e: M.CE) -> Type:
  match e:
    case M.CRd{}:
      Unit
    case M.CWr{v}:
      Unit
    case M.CSt{k}:
      Unit
    case M.CDw{v}:
      Empty

def canon_k(k: M.K, st: M.St, pr: M.Pr, h: Nat, d: Nat, g: Nat, hw: Bool, pf: Bool, used: Nat, mk: Bool)
  -> {M.kstep(k, M.Ch{st, pr, M.Free{}, M.pd0(), h, d, g, hw, pf, used, mk}) == M.Ch{st, pr, M.Free{}, M.pd0(), h, d, g, hw, pf, used, mk} : M.Ch}:
  match k:
    case M.KLC{}:
      {==}
    case M.KAR{}:
      {==}
    case M.KF{wr}:
      match wr:
        case True{}:
          {==}
        case False{}:
          {==}
    case M.KS{wr}:
      match wr:
        case True{}:
          {==}
        case False{}:
          {==}
    case M.KLk{}:
      {==}

# with nobody in the handler, a fault step does nothing
def quiet_k(ch: M.Ch, q: M.Quiet(ch), k: M.K) -> ({M.kstep(k, ch) == ch : M.Ch} & M.Quiet(ch)):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match lk:
        case M.Free{}:
          match pd:
            case M.Pd{lc, ar, f0, f1, s0, s1}:
              match lc:
                case 1n+p:
                  match q:
                    case (fr, z1):
                      match z1:
                        case (zl, z2):
                          match zl:
                case 0n:
                  match ar:
                    case 1n+p:
                      match q:
                        case (fr, z1):
                          match z1:
                            case (zl, z2):
                              match z2:
                                case (za, z3):
                                  match za:
                    case 0n:
                      match f0:
                        case 1n+p:
                          match q:
                            case (fr, z1):
                              match z1:
                                case (zl, z2):
                                  match z2:
                                    case (za, z3):
                                      match z3:
                                        case (zf0, z4):
                                          match zf0:
                        case 0n:
                          match f1:
                            case 1n+p:
                              match q:
                                case (fr, z1):
                                  match z1:
                                    case (zl, z2):
                                      match z2:
                                        case (za, z3):
                                          match z3:
                                            case (zf0, z4):
                                              match z4:
                                                case (zf1, z5):
                                                  match zf1:
                            case 0n:
                              match s0:
                                case 1n+p:
                                  match q:
                                    case (fr, z1):
                                      match z1:
                                        case (zl, z2):
                                          match z2:
                                            case (za, z3):
                                              match z3:
                                                case (zf0, z4):
                                                  match z4:
                                                    case (zf1, z5):
                                                      match z5:
                                                        case (zs0, zs1):
                                                          match zs0:
                                case 0n:
                                  match s1:
                                    case 1n+p:
                                      match q:
                                        case (fr, z1):
                                          match z1:
                                            case (zl, z2):
                                              match z2:
                                                case (za, z3):
                                                  match z3:
                                                    case (zf0, z4):
                                                      match z4:
                                                        case (zf1, z5):
                                                          match z5:
                                                            case (zs0, zs1):
                                                              match zs1:
                                    case 0n:
                                      (canon_k(k, st, pr, h, d, g, hw, pf, used, mk),
                                        (Unit{}, (Unit{}, (Unit{}, (Unit{}, (Unit{}, (Unit{}, Unit{})))))))
        case M.SCp{w}:
          match pd:
            case M.Pd{lc, ar, f0, f1, s0, s1}:
              match q:
                case (fr, z1):
                  match fr:
        case M.SOp{w}:
          match pd:
            case M.Pd{lc, ar, f0, f1, s0, s1}:
              match q:
                case (fr, z1):
                  match fr:
        case M.FOp{w}:
          match pd:
            case M.Pd{lc, ar, f0, f1, s0, s1}:
              match q:
                case (fr, z1):
                  match fr:

def out_k.fin(+k: M.K, +ch: M.Ch, l4: M.L4c(ch), y: Ck.OI.b(ch), r: ({M.kstep(k, ch) == ch : M.Ch} & M.Quiet(ch))) -> Ck.CO(M.kstep(k, ch)):
  match r:
    case (e, q):
      %Equal.sym(M.Ch, M.kstep(k, ch), ch, e) : Ck.CO(_)
      (l4, (q, y))

def out_k(+k: M.K, +ch: M.Ch, i: Ck.CO(ch)) -> Ck.CO(M.kstep(k, ch)):
  match i:
    case (l4, x):
      match x:
        case (q, y):
          out_k.fin(k, ch, l4, y, quiet_k(ch, q, k))

# a host event above n: reads and writes land (a write sets hw), and
# no thread is in the handler there
def out_ev(e: M.CE, +ch: M.Ch, ok: HostCE(e), i: Ck.CO(ch)) -> Ck.CO(M.cev(True{}, e, ch)):
  match e:
    case M.CRd{}:
      match ch:
        case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
          match st:
            case M.Dy{}:
              match pr:
                case M.PW{}:
                  i
                case M.PN{}:
                  match i:
                    case (l4, x):
                      match x:
                        case (q, y):
                          match y:
                            case (w, z):
                              match w:
                case M.PR{}:
                  match i:
                    case (l4, x):
                      match x:
                        case (q, y):
                          match y:
                            case (w, z):
                              match w:
            case M.Cl{}:
              match i:
                case (l4, x):
                  match x:
                    case (q, y):
                      match y:
            case M.Sl{}:
              match i:
                case (l4, x):
                  match x:
                    case (q, y):
                      match y:
            case M.Fe{}:
              match i:
                case (l4, x):
                  match x:
                    case (q, y):
                      match y:
    case M.CWr{+v}:
      match ch:
        case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
          match st:
            case M.Dy{}:
              match pr:
                case M.PW{}:
                  match pd:
                    case M.Pd{lc, ar, f0, f1, s0, s1}:
                      match i:
                        case (l4, x):
                          match x:
                            case (q, y):
                              (l4, (q, (Unit{}, ({==}, Unit{}))))
                case M.PN{}:
                  match i:
                    case (l4, x):
                      match x:
                        case (q, y):
                          match y:
                            case (w, z):
                              match w:
                case M.PR{}:
                  match i:
                    case (l4, x):
                      match x:
                        case (q, y):
                          match y:
                            case (w, z):
                              match w:
            case M.Cl{}:
              match i:
                case (l4, x):
                  match x:
                    case (q, y):
                      match y:
            case M.Sl{}:
              match i:
                case (l4, x):
                  match x:
                    case (q, y):
                      match y:
            case M.Fe{}:
              match i:
                case (l4, x):
                  match x:
                    case (q, y):
                      match y:
    case M.CSt{k}:
      out_k(k, ch, i)
    case M.CDw{v}:
      match ok:

# swept under n between turns: a dirty chunk
def out_host(ch: M.Ch, i: Ck.CO(ch)) -> Ck.CH(ch):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match st:
        case M.Dy{}:
          match lk:
            case M.Free{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, x):
                      match x:
                        case (q, y):
                          match y:
                            case (w, z):
                              match z:
                                case (hg, dg):
                                  (l4, (Unit{}, (w, hg)))
            case M.SCp{wr}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, x):
                      match x:
                        case (q, y):
                          match q:
                            case (fr, zs):
                              match fr:
            case M.SOp{wr}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, x):
                      match x:
                        case (q, y):
                          match q:
                            case (fr, zs):
                              match fr:
            case M.FOp{wr}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, x):
                      match x:
                        case (q, y):
                          match q:
                            case (fr, zs):
                              match fr:
        case M.Cl{}:
          match i:
            case (l4, x):
              match x:
                case (q, y):
                  match y:
        case M.Sl{}:
          match i:
            case (l4, x):
              match x:
                case (q, y):
                  match y:
        case M.Fe{}:
          match i:
            case (l4, x):
              match x:
                case (q, y):
                  match y:

# swept under n in a turn, not written by the host above n: its device
# bytes are the last
def out_dev(ch: M.Ch, i: Ck.CO(ch), nh: M.NoHw(ch)) -> Ck.CD(ch):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match st:
        case M.Dy{}:
          match pd:
            case M.Pd{lc, ar, f0, f1, s0, s1}:
              match hw:
                case True{}:
                  match nh:
                case False{}:
                  match i:
                    case (l4, x):
                      match x:
                        case (q, y):
                          match y:
                            case (w, z):
                              match z:
                                case (hg, dg):
                                  (l4, (q, dg))
        case M.Cl{}:
          match i:
            case (l4, x):
              match x:
                case (q, y):
                  match y:
        case M.Sl{}:
          match i:
            case (l4, x):
              match x:
                case (q, y):
                  match y:
        case M.Fe{}:
          match i:
            case (l4, x):
              match x:
                case (q, y):
                  match y:

# The lists
# ---------

def DevCE(e: M.CE) -> Type:
  match e:
    case M.CRd{}:
      Empty
    case M.CWr{v}:
      Empty
    case M.CSt{k}:
      Empty
    case M.CDw{v}:
      Unit

# host events between turns, device stores in one
def EOk(ph: M.Ph, e: M.CE) -> Type:
  match ph:
    case M.Host{}:
      HostCE(e)
    case M.Dev{}:
      DevCE(e)

def cev_in_ok(ph: M.Ph, e: M.CE, ch: M.Ch, ok: EOk(ph, e), i: Ck.CI(ph, ch)) -> Ck.CI(ph, M.cev(False{}, e, ch)):
  match ph:
    case M.Host{}:
      match e:
        case M.CRd{}:
          Ck.read_ok(ch, i)
        case M.CWr{v}:
          Ck.write_ok(False{}, v, ch, i)
        case M.CSt{k}:
          Ck.kstep_ok(k, ch, i)
        case M.CDw{v}:
          match ok:
    case M.Dev{}:
      match e:
        case M.CRd{}:
          match ok:
        case M.CWr{v}:
          match ok:
        case M.CSt{k}:
          match ok:
        case M.CDw{v}:
          Ck.dwrite_ok(v, ch, i)

def upd_i_ok(xs: List<&2, M.Ch>, c: Nat, +e: M.CE, +ph: M.Ph, ok: EOk(ph, e), a: Ck.AI(ph, xs)) -> Ck.AI(ph, M.upd_i(xs, c, e)):
  match xs c:
    case Nil{} _:
      Unit{}
    case h <> t 0n:
      match a:
        case (ah, at):
          (cev_in_ok(ph, e, h, ok, ah), at)
    case h <> t 1n+p:
      match a:
        case (ah, at):
          (ah, upd_i_ok(t, p, e, ph, ok, at))

def upd_at_ok(xs: List<&2, M.Ch>, c: Nat, +e: M.CE, ok: HostCE(e), a: Ck.AO(xs)) -> Ck.AO(M.upd_at(xs, c, e)):
  match xs c:
    case Nil{} _:
      Unit{}
    case h <> t 0n:
      match a:
        case (ah, at):
          (out_ev(e, h, ok, ah), at)
    case h <> t 1n+p:
      match a:
        case (ah, at):
          (ah, upd_at_ok(t, p, e, ok, at))

def upd_o_ok(n: Nat, c: Nat, +e: M.CE, xs: List<&2, M.Ch>, ok: HostCE(e), a: Ck.AO(xs)) -> Ck.AO(M.upd_o(n, c, e, xs)):
  match n c:
    case 0n c:
      upd_at_ok(xs, c, e, ok, a)
    case 1n+m 0n:
      a
    case 1n+m 1n+p:
      upd_o_ok(m, p, e, xs, ok, a)

# a store under n leaves the chunks above it alone
def upd_o_skip(n: Nat, c: Nat, +e: M.CE, xs: List<&2, M.Ch>, lt: M.LE(1n+c, n)) -> {M.upd_o(n, c, e, xs) == xs : List<&2, M.Ch>}:
  match n c:
    case 0n c:
      match lt:
    case 1n+m 0n:
      {==}
    case 1n+m 1n+p:
      upd_o_skip(m, p, e, xs, lt)

def skip_ao(+n: Nat, +c: Nat, +e: M.CE, +xs: List<&2, M.Ch>, lt: M.LE(1n+c, n), a: Ck.AO(xs)) -> Ck.AO(M.upd_o(n, c, e, xs)):
  %Equal.sym(List<&2, M.Ch>, M.upd_o(n, c, e, xs), xs, upd_o_skip(n, c, e, xs, lt)) : Ck.AO(_)
  a

def en1s_ok(xs: List<&2, M.Ch>, q: M.AllQ(xs), a: Ck.AI(M.Host{}, xs)) -> Ck.AI(M.Dev{}, M.en1s(xs)):
  match xs:
    case Nil{}:
      Unit{}
    case h <> t:
      match q:
        case (qh, qt):
          match a:
            case (ah, at):
              (Ck.en1_ok(h, qh, ah), en1s_ok(t, qt, at))

# whatever the prefetch set
def lv1s_ok(xs: List<&2, M.Ch>, ps: List<&2, Bool>, a: Ck.AI(M.Dev{}, xs)) -> Ck.AI(M.Host{}, M.lv1s(xs, ps)):
  match xs:
    case Nil{}:
      Unit{}
    case h <> t:
      match ps:
        case Nil{}:
          match a:
            case (ah, at):
              (Ck.lv1_ok(False{}, h, ah), lv1s_ok(t, Nil{}, at))
        case p <> q:
          match a:
            case (ah, at):
              (Ck.lv1_ok(p, h, ah), lv1s_ok(t, q, at))

def pcons(-ph: M.Ph, -h: M.Ch, -xs: List<&2, M.Ch>, -ys: List<&2, M.Ch>, x: Ck.CI(ph, h), r: (Ck.AI(ph, xs) & Ck.AO(ys)))
  -> (Ck.AI(ph, h <> xs) & Ck.AO(ys)):
  match r:
    case (a, b):
      ((x, a), b)

def take_ok(ph: M.Ph, xs: List<&2, M.Ch>, m: Nat, sw: M.Swept(ph, m, xs), a: Ck.AO(xs))
  -> (Ck.AI(ph, List.take(&2, M.Ch, xs, m)) & Ck.AO(List.drop(&2, M.Ch, xs, m))):
  match ph:
    case M.Host{}:
      match xs m:
        case Nil{} _:
          (Unit{}, Unit{})
        case h <> t 0n:
          (Unit{}, a)
        case h <> t 1n+p:
          match a:
            case (ah, at):
              pcons(M.Host{}, h, List.take(&2, M.Ch, t, p), List.drop(&2, M.Ch, t, p), out_host(h, ah),
                take_ok(M.Host{}, t, p, Unit{}, at))
    case M.Dev{}:
      match xs m:
        case Nil{} _:
          (Unit{}, Unit{})
        case h <> t 0n:
          (Unit{}, a)
        case h <> t 1n+p:
          match sw:
            case (nh, sw2):
              match a:
                case (ah, at):
                  pcons(M.Dev{}, h, List.take(&2, M.Ch, t, p), List.drop(&2, M.Ch, t, p), out_dev(h, ah, nh),
                    take_ok(M.Dev{}, t, p, sw2, at))

# a bump that n only grows allows
def rs_ok(+ph: M.Ph, ins: List<&2, M.Ch>, m: Nat, +outs: List<&2, M.Ch>, b: M.BOk(ph, ins, m, outs), ai: Ck.AI(ph, ins), ao: Ck.AO(outs))
  -> (Ck.AI(ph, M.rs_in(ins, m, outs)) & Ck.AO(M.rs_out(ins, m, outs))):
  match ins:
    case Nil{}:
      take_ok(ph, outs, m, b, ao)
    case h <> t:
      match m:
        case 0n:
          match b:
        case 1n+p:
          match ai:
            case (ah, at):
              pcons(ph, h, M.rs_in(t, p, outs), M.rs_out(t, p, outs), ah, rs_ok(ph, t, p, outs, b, at, ao))

# The system
# ----------

def lv_ok(ins: List<&2, M.Ch>, outs: List<&2, M.Ch>, r: List<&2, Bool> & M.Hs, ai: Ck.AI(M.Dev{}, ins), ao: Ck.AO(outs))
  -> Ck.Inv(M.lv.fin(M.Dev{}, ins, outs, r)):
  match r:
    case (ps, hs):
      (lv1s_ok(ins, ps, ai), ao)

def inv_step(s: M.Sys, e: M.Ev, i: Ck.Inv(s), ok: M.Ok(s, e)) -> Ck.Inv(M.step(s, e)):
  match s:
    case M.Sys{ph, +ins, +outs, +hs}:
      match ph:
        case M.Host{}:
          match e:
            case M.Rd{+c}:
              match i:
                case (ai, ao):
                  (upd_i_ok(ins, c, M.CRd{}, M.Host{}, Unit{}, ai), upd_o_ok(M.len(ins), c, M.CRd{}, outs, Unit{}, ao))
            case M.Wr{+c, +v}:
              match i:
                case (ai, ao):
                  (upd_i_ok(ins, c, M.CWr{v}, M.Host{}, Unit{}, ai), upd_o_ok(M.len(ins), c, M.CWr{v}, outs, Unit{}, ao))
            case M.Stp{+c, +k}:
              match i:
                case (ai, ao):
                  (upd_i_ok(ins, c, M.CSt{k}, M.Host{}, Unit{}, ai), upd_o_ok(M.len(ins), c, M.CSt{k}, outs, Unit{}, ao))
            case M.DWr{+c, +v}:
              match ok:
                case (u, lt):
                  match u:
            case M.Ent{k}:
              match i:
                case (ai, ao):
                  match ok:
                    case (u, qi):
                      (en1s_ok(ins, qi, ai), ao)
            case M.Bmp{+m}:
              match i:
                case (ai, ao):
                  rs_ok(M.Host{}, ins, m, outs, ok, ai, ao)
            case M.Lv{}:
              match ok:
        case M.Dev{}:
          match e:
            case M.Rd{+c}:
              match ok:
            case M.Wr{+c, +v}:
              match ok:
            case M.Stp{+c, +k}:
              match ok:
            case M.DWr{+c, +v}:
              match i:
                case (ai, ao):
                  match ok:
                    case (u, lt):
                      (upd_i_ok(ins, c, M.CDw{v}, M.Dev{}, Unit{}, ai), skip_ao(M.len(ins), c, M.CDw{v}, outs, lt, ao))
            case M.Ent{k}:
              match ok:
                case (u, qs):
                  match u:
            case M.Bmp{+m}:
              match i:
                case (ai, ao):
                  rs_ok(M.Dev{}, ins, m, outs, ok, ai, ao)
            case M.Lv{}:
              match i:
                case (ai, ao):
                  lv_ok(ins, outs, M.lv_hs(M.len(ins), Nat.add(M.len(ins), M.len(outs)), hs), ai, ao)

def inv_run(es: List<&2, M.Ev>, +s: M.Sys, i: Ck.Inv(s), v: M.Valid(es, s)) -> Ck.Inv(M.run(es, s)):
  match es:
    case Nil{}:
      i
    case +e <> t:
      match v:
        case (ok, vt):
          inv_run(t, M.step(s, e), inv_step(s, e, i, ok), vt)

def rep_in(n: Nat) -> Ck.AI(M.Host{}, List.replicate(M.Ch, n, M.ch0())):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      (({==}, (Unit{}, (Unit{}, {==}))), rep_in(p))

def rep_out(n: Nat) -> Ck.AO(List.replicate(M.Ch, n, M.ch0())):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      (({==}, ((Unit{}, (Unit{}, (Unit{}, (Unit{}, (Unit{}, (Unit{}, Unit{})))))), (Unit{}, ({==}, {==})))), rep_out(p))

def inv_init(+n0: Nat, +m0: Nat, +pfm: Nat) -> Ck.Inv(M.init(n0, m0, pfm)):
  (rep_in(n0), rep_out(m0))

# every trace Valid allows keeps Ck.Inv
def inv_trace(+n0: Nat, +m0: Nat, +pfm: Nat, es: List<&2, M.Ev>, v: M.Valid(es, M.init(n0, m0, pfm))) -> Ck.Inv(M.run(es, M.init(n0, m0, pfm))):
  inv_run(es, M.init(n0, m0, pfm), inv_init(n0, m0, pfm), v)

# The laws, off Ck.Inv
# -----------------

# L1: a readable chunk under n holds the last write
def l1_op(w: Bool, -st: M.St, pr: M.Pr, -lk: M.Lk, -pd: M.Pd, -h: Nat, -d: Nat, -g: Nat, -hw: Bool, -pf: Bool, -used: Nat, -mk: Bool,
  x: Ck.HI.op(w, pr, h, d, g)) -> M.L1c(M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}):
  match w:
    case True{}:
      match pr:
        case M.PN{}:
          Unit{}
        case M.PR{}:
          match x:
            case (r, e):
              match r:
        case M.PW{}:
          match x:
            case (r, e):
              e
    case False{}:
      match pr:
        case M.PN{}:
          Unit{}
        case M.PR{}:
          match x:
            case (r, y):
              match y:
                case (hd, dg):
                  Ck.tr(h, d, g, hd, dg)
        case M.PW{}:
          match x:
            case (r, e):
              match r:

# the trapping cases hold for nothing to show
def l1_n(-st: M.St, pr: M.Pr, -lk: M.Lk, -pd: M.Pd, -h: Nat, -d: Nat, -g: Nat, -hw: Bool, -pf: Bool, -used: Nat, -mk: Bool,
  n: M.NoAcc(pr)) -> M.L1c(M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}):
  match pr:
    case M.PN{}:
      Unit{}
    case M.PR{}:
      match n:
    case M.PW{}:
      match n:

def l1_ch(ch: M.Ch, i: Ck.CH(ch)) -> M.L1c(ch):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match st:
        case M.Dy{}:
          match pr:
            case M.PN{}:
              Unit{}
            case M.PR{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (fr, x):
                          match x:
                            case (w, e):
                              match w:
            case M.PW{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (fr, x):
                          match x:
                            case (w, e):
                              e
        case M.Cl{}:
          match pr:
            case M.PN{}:
              Unit{}
            case M.PR{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (fr, x):
                          match x:
                            case (e, y):
                              e
            case M.PW{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (fr, x):
                          match x:
                            case (e, y):
                              e
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
                            case (n, e):
                              l1_n(M.Sl{}, pr, M.Free{}, M.Pd{lc, ar, f0, f1, s0, s1}, h, d, g, hw, pf, used, mk, n)
            case M.SCp{w}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (nc, x):
                          match x:
                            case (n, e):
                              l1_n(M.Sl{}, pr, M.SCp{w}, M.Pd{lc, ar, f0, f1, s0, s1}, h, d, g, hw, pf, used, mk, n)
            case M.SOp{w}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (nc, x):
                          l1_op(w, M.Sl{}, pr, M.SOp{w}, M.Pd{lc, ar, f0, f1, s0, s1}, h, d, g, hw, pf, used, mk, x)
            case M.FOp{w}:
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
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (nc, x):
                          match x:
                            case (n, e):
                              l1_n(M.Fe{}, pr, M.Free{}, M.Pd{lc, ar, f0, f1, s0, s1}, h, d, g, hw, pf, used, mk, n)
            case M.SCp{w}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (nc, x):
                          match x:
            case M.SOp{w}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (nc, x):
                          match x:
            case M.FOp{w}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (nc, x):
                          l1_op(w, M.Fe{}, pr, M.FOp{w}, M.Pd{lc, ar, f0, f1, s0, s1}, h, d, g, hw, pf, used, mk, x)

def l1_out(ch: M.Ch, i: Ck.CO(ch)) -> M.L1c(ch):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match st:
        case M.Dy{}:
          match pr:
            case M.PN{}:
              Unit{}
            case M.PR{}:
              match i:
                case (l4, x):
                  match x:
                    case (q, y):
                      match y:
                        case (w, z):
                          match w:
            case M.PW{}:
              match i:
                case (l4, x):
                  match x:
                    case (q, y):
                      match y:
                        case (w, z):
                          match z:
                            case (hg, r):
                              hg
        case M.Cl{}:
          match i:
            case (l4, x):
              match x:
                case (q, y):
                  match y:
        case M.Sl{}:
          match i:
            case (l4, x):
              match x:
                case (q, y):
                  match y:
        case M.Fe{}:
          match i:
            case (l4, x):
              match x:
                case (q, y):
                  match y:

# L2 between turns
def l2h_ch(ch: M.Ch, i: Ck.CH(ch)) -> M.L2h(ch):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match st:
        case M.Dy{}:
          match pr:
            case M.PN{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (fr, x):
                          match x:
                            case (w, e):
                              match w:
            case M.PR{}:
              (Unit{}, Unit{})
            case M.PW{}:
              (Unit{}, Unit{})
        case M.Cl{}:
          (Unit{}, Unit{})
        case M.Sl{}:
          match lk:
            case M.Free{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (nc, x):
                          (x, Unit{})
            case M.SCp{w}:
              (Unit{}, Unit{})
            case M.SOp{w}:
              (Unit{}, Unit{})
            case M.FOp{w}:
              (Unit{}, Unit{})
        case M.Fe{}:
          (Unit{}, Unit{})

# L2 in a turn
def l2d_ch(ch: M.Ch, i: Ck.CD(ch)) -> M.L2d(ch):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match pd:
        case M.Pd{lc, ar, f0, f1, s0, s1}:
          match i:
            case (l4, x):
              match x:
                case (q, dg):
                  dg

def l3_ch(ch: M.Ch, i: Ck.CH(ch)) -> M.L3c(ch):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match st:
        case M.Fe{}:
          match lk:
            case M.Free{}:
              match pd:
                case M.Pd{lc, ar, f0, f1, s0, s1}:
                  match i:
                    case (l4, hi):
                      match hi:
                        case (nc, x):
                          x
            case M.SCp{w}:
              Unit{}
            case M.SOp{w}:
              Unit{}
            case M.FOp{w}:
              Unit{}
        case M.Dy{}:
          Unit{}
        case M.Cl{}:
          Unit{}
        case M.Sl{}:
          Unit{}

def l4_in(ph: M.Ph, ch: M.Ch, i: Ck.CI(ph, ch)) -> M.L4c(ch):
  match ph:
    case M.Host{}:
      match i:
        case (l4, x):
          l4
    case M.Dev{}:
      match i:
        case (l4, x):
          l4

def all_l1_in(xs: List<&2, M.Ch>, a: Ck.AI(M.Host{}, xs)) -> M.All(M.KL1{}, xs):
  match xs:
    case Nil{}:
      Unit{}
    case h <> t:
      match a:
        case (ah, at):
          (l1_ch(h, ah), all_l1_in(t, at))

def all_l1_out(xs: List<&2, M.Ch>, a: Ck.AO(xs)) -> M.All(M.KL1{}, xs):
  match xs:
    case Nil{}:
      Unit{}
    case h <> t:
      match a:
        case (ah, at):
          (l1_out(h, ah), all_l1_out(t, at))

def all_l2h(xs: List<&2, M.Ch>, a: Ck.AI(M.Host{}, xs)) -> M.All(M.KL2h{}, xs):
  match xs:
    case Nil{}:
      Unit{}
    case h <> t:
      match a:
        case (ah, at):
          (l2h_ch(h, ah), all_l2h(t, at))

def all_l2d(xs: List<&2, M.Ch>, a: Ck.AI(M.Dev{}, xs)) -> M.All(M.KL2d{}, xs):
  match xs:
    case Nil{}:
      Unit{}
    case h <> t:
      match a:
        case (ah, at):
          (l2d_ch(h, ah), all_l2d(t, at))

def all_l3(xs: List<&2, M.Ch>, a: Ck.AI(M.Host{}, xs)) -> M.All(M.KL3{}, xs):
  match xs:
    case Nil{}:
      Unit{}
    case h <> t:
      match a:
        case (ah, at):
          (l3_ch(h, ah), all_l3(t, at))

def all_l4_in(+ph: M.Ph, xs: List<&2, M.Ch>, a: Ck.AI(ph, xs)) -> M.All(M.KL4{}, xs):
  match xs:
    case Nil{}:
      Unit{}
    case h <> t:
      match a:
        case (ah, at):
          (l4_in(ph, h, ah), all_l4_in(ph, t, at))

def all_l4_out(xs: List<&2, M.Ch>, a: Ck.AO(xs)) -> M.All(M.KL4{}, xs):
  match xs:
    case Nil{}:
      Unit{}
    case h <> t:
      match a:
        case (ah, at):
          match ah:
            case (l4, x):
              (l4, all_l4_out(t, at))

def l1_of(s: M.Sys, i: Ck.Inv(s)) -> M.L1(s):
  match s:
    case M.Sys{ph, ins, outs, hs}:
      match ph:
        case M.Host{}:
          match i:
            case (ai, ao):
              (all_l1_in(ins, ai), all_l1_out(outs, ao))
        case M.Dev{}:
          Unit{}

def l2_of(s: M.Sys, i: Ck.Inv(s)) -> M.L2(s):
  match s:
    case M.Sys{ph, ins, outs, hs}:
      match ph:
        case M.Host{}:
          match i:
            case (ai, ao):
              all_l2h(ins, ai)
        case M.Dev{}:
          match i:
            case (ai, ao):
              all_l2d(ins, ai)

def l3_of(s: M.Sys, i: Ck.Inv(s)) -> M.L3(s):
  match s:
    case M.Sys{ph, ins, outs, hs}:
      match ph:
        case M.Host{}:
          match i:
            case (ai, ao):
              all_l3(ins, ai)
        case M.Dev{}:
          Unit{}

def l4_of(s: M.Sys, i: Ck.Inv(s)) -> M.L4(s):
  match s:
    case M.Sys{+ph, ins, outs, hs}:
      match i:
        case (ai, ao):
          (all_l4_in(ph, ins, ai), all_l4_out(outs, ao))

def Laws.l1_read_fresh(n0, m0, pfm, es, v):
  l1_of(M.run(es, M.init(n0, m0, pfm)), inv_trace(n0, m0, pfm, es, v))

def Laws.l2_no_lost_write(n0, m0, pfm, es, v):
  l2_of(M.run(es, M.init(n0, m0, pfm)), inv_trace(n0, m0, pfm, es, v))

def Laws.l3_prefetch_current(n0, m0, pfm, es, v):
  l3_of(M.run(es, M.init(n0, m0, pfm)), inv_trace(n0, m0, pfm, es, v))

def Laws.l4_used_once(n0, m0, pfm, es, v):
  l4_of(M.run(es, M.init(n0, m0, pfm)), inv_trace(n0, m0, pfm, es, v))
