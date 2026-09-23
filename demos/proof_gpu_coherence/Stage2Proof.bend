# proof_gpu_coherence -- the proofs of Stage2Laws.bend. Between turns
# the invariant is stage 1's; in a turn a chunk under the ceiling is
# also one the leave may keep, unless marked (Coh). The host events,
# the bump between turns and the stage-1 leave of a chunk in I are
# PROOF.bend's and Chunk.bend's lemmas.
import Base
import ./main.bend as M
import ./Chunk.bend as Ck
import ./PROOF.bend as P
import ./Stage2.bend as S
import ./Stage2Laws.bend as Laws2

# The invariant
# -------------

def CD1(+ch: M.Ch) -> Type:
  (Ck.CD(ch) & S.Coh(ch))

# in a turn: t chunks under the ceiling (all of them under n), then
# stage 1's
def AD(t: Nat, xs: List<&2, M.Ch>) -> Type:
  match t:
    case 0n:
      Ck.AI(M.Dev{}, xs)
    case 1n+u:
      match xs:
        case Nil{}:
          Empty
        case h <> r:
          (CD1(h) & AD(u, r))

def Inv2(s: M.Sys) -> Type:
  match s:
    case M.Sys{ph, ins, outs, hs}:
      match ph:
        case M.Host{}:
          (Ck.AI(M.Host{}, ins) & Ck.AO(outs))
        case M.Dev{}:
          (AD(S.Hs.tw(hs), ins) & Ck.AO(outs))

# The enter
# ---------

def en2_ok(ch: M.Ch, q: M.Quiet(ch), i: Ck.CH(ch)) -> CD1(S.en2(ch)):
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
                          ((l4, (q, hg)), ({==}, Unit{}))
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
                                case (+hd, z):
                                  ((l4, (q, Ck.tr(d, h, g, Ck.sym(h, d, hd), hg))), (hd, Unit{}))
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
                              ((l4, (q, dg)), n)
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
                                  ((l4, (q, dg)), (hd, n))
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

def en2_k0(ch: M.Ch, q: M.Quiet(ch), i: Ck.CH(ch)) -> S.K0c(S.en2(ch)):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match st:
        case M.Dy{}:
          {==}
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
                                  hd
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
          Unit{}
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
                                  hd
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

def cd_of(-ch: M.Ch, c: CD1(ch)) -> Ck.CD(ch):
  match c:
    case (cd, coh):
      cd

def en2s_ai(xs: List<&2, M.Ch>, q: M.AllQ(xs), a: Ck.AI(M.Host{}, xs)) -> Ck.AI(M.Dev{}, S.en2s(xs)):
  match xs:
    case Nil{}:
      Unit{}
    case h <> t:
      match q:
        case (qh, qt):
          match a:
            case (ah, at):
              (cd_of(S.en2(h), en2_ok(h, qh, ah)), en2s_ai(t, qt, at))

# the enter: t (under n) chunks under the ceiling
def en2s_ok(t: Nat, xs: List<&2, M.Ch>, q: M.AllQ(xs), a: Ck.AI(M.Host{}, xs), le: M.LE(t, M.len(xs))) -> AD(t, S.en2s(xs)):
  match t:
    case 0n:
      en2s_ai(xs, q, a)
    case 1n+u:
      match xs:
        case Nil{}:
          match le:
        case h <> r:
          match q:
            case (qh, qr):
              match a:
                case (ah, ar):
                  (en2_ok(h, qh, ah), en2s_ok(u, r, qr, ar, le))

def en2s_k0(xs: List<&2, M.Ch>, q: M.AllQ(xs), a: Ck.AI(M.Host{}, xs)) -> S.AllK0(S.en2s(xs)):
  match xs:
    case Nil{}:
      Unit{}
    case h <> t:
      match q:
        case (qh, qt):
          match a:
            case (ah, at):
              (en2_k0(h, qh, ah), en2s_k0(t, qt, at))

# A device store
# --------------

def dw2_cd(+v: Nat, m: Bool, ch: M.Ch, i: Ck.CD(ch)) -> Ck.CD(S.dw2(v, m, ch)):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match pd:
        case M.Pd{lc, ar, f0, f1, s0, s1}:
          match i:
            case (l4, x):
              match x:
                case (q, e):
                  (l4, (q, {==}))

# a marking store: its chunk is marked
def dw2_mk(+v: Nat, ch: M.Ch, i: Ck.CD(ch)) -> CD1(S.dw2(v, True{}, ch)):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      match mk:
        case True{}:
          (dw2_cd(v, True{}, M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, True{}}, i), Unit{})
        case False{}:
          (dw2_cd(v, True{}, M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, False{}}, i), Unit{})

def dw2_ai(xs: List<&2, M.Ch>, c: Nat, +v: Nat, +m: Bool, a: Ck.AI(M.Dev{}, xs)) -> Ck.AI(M.Dev{}, S.upd2(xs, c, v, m)):
  match xs c:
    case Nil{} _:
      Unit{}
    case h <> t 0n:
      match a:
        case (ah, at):
          (dw2_cd(v, m, h, ah), at)
    case h <> t 1n+p:
      match a:
        case (ah, at):
          (ah, dw2_ai(t, p, v, m, at))

def mk_dn(m: Bool, -u: Nat, -p: Nat, ok: S.MkOk(m, 1n+u, 1n+p)) -> S.MkOk(m, u, p):
  match m:
    case True{}:
      Unit{}
    case False{}:
      ok

def dw2_ok(t: Nat, xs: List<&2, M.Ch>, c: Nat, +v: Nat, +m: Bool, ok: S.MkOk(m, t, c), a: AD(t, xs)) -> AD(t, S.upd2(xs, c, v, m)):
  match t:
    case 0n:
      dw2_ai(xs, c, v, m, a)
    case 1n+u:
      match xs:
        case Nil{}:
          match a:
        case h <> r:
          match c:
            case 0n:
              match m:
                case True{}:
                  match a:
                    case (ah, ar):
                      match ah:
                        case (cd, coh):
                          (dw2_mk(v, h, cd), ar)
                case False{}:
                  match ok:
            case 1n+p:
              match a:
                case (ah, ar):
                  (ah, dw2_ok(u, r, p, v, m, mk_dn(m, u, p, ok), ar))

def adcons(-u: Nat, -h: M.Ch, -xs: List<&2, M.Ch>, -ys: List<&2, M.Ch>, x: CD1(h), r: (AD(u, xs) & Ck.AO(ys)))
  -> (AD(1n+u, h <> xs) & Ck.AO(ys)):
  match r:
    case (a, b):
      ((x, a), b)

# A bump in a turn: what it sweeps in is above the ceiling
def rs2_ok(t: Nat, ins: List<&2, M.Ch>, m: Nat, +outs: List<&2, M.Ch>, b: M.BOk(M.Dev{}, ins, m, outs), a: AD(t, ins), ao: Ck.AO(outs))
  -> (AD(t, M.rs_in(ins, m, outs)) & Ck.AO(M.rs_out(ins, m, outs))):
  match t:
    case 0n:
      P.rs_ok(M.Dev{}, ins, m, outs, b, a, ao)
    case 1n+u:
      match ins:
        case Nil{}:
          match a:
        case h <> r:
          match m:
            case 0n:
              match b:
            case 1n+p:
              match a:
                case (ah, ar):
                  adcons(u, h, M.rs_in(r, p, outs), M.rs_out(r, p, outs), ah, rs2_ok(u, r, p, outs, b, ar, ao))

# The leave
# ---------

# an unmarked chunk under the ceiling: kept, or a STALE one fetched
def lv2k(mk: Bool, p: Bool, st: M.St, pr: M.Pr, lk: M.Lk, pd: M.Pd, h: Nat, d: Nat, g: Nat, hw: Bool, pf: Bool, used: Nat,
  i: Ck.CD(M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}), c: S.Coh(M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}))
  -> Ck.CH(S.lv2h.go(mk, p, M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk})):
  match mk:
    case True{}:
      Ck.lv1_ok(p, M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, True{}}, i)
    case False{}:
      match st:
        case M.Sl{}:
          Ck.lv1_ok(p, M.Ch{M.Sl{}, pr, lk, pd, h, d, g, hw, pf, used, False{}}, i)
        case M.Dy{}:
          match c:
        case M.Cl{}:
          match pr:
            case M.PN{}:
              match c:
                case (e, r):
                  match r:
            case M.PR{}:
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
                                      match c:
                                        case (+hd, r):
                                          (l4, (fr, (Ck.tr(h, d, g, hd, dg), (hd, za))))
            case M.PW{}:
              match c:
                case (e, r):
                  match r:
        case M.Fe{}:
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
                                      match c:
                                        case (hd, n):
                                          (l4, ((zl, za), (n, (hd, dg))))
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

def lv2o_ok(p: Bool, ch: M.Ch, i: Ck.CD(ch), c: S.Coh(ch)) -> Ck.CH(S.lv2h(p, ch)):
  match ch:
    case M.Ch{st, pr, lk, pd, h, d, g, hw, pf, used, mk}:
      lv2k(mk, p, st, pr, lk, pd, h, d, g, hw, pf, used, i, c)

def lv2h_ok(p: Bool, ch: M.Ch, i: CD1(ch)) -> Ck.CH(S.lv2h(p, ch)):
  match i:
    case (cd, c):
      lv2o_ok(p, ch, cd, c)

# whatever the prefetch set
def lv2s_ok(t: Nat, xs: List<&2, M.Ch>, ps: List<&2, Bool>, a: AD(t, xs)) -> Ck.AI(M.Host{}, S.lv2s(t, xs, ps)):
  match t:
    case 0n:
      P.lv1s_ok(xs, ps, a)
    case 1n+u:
      match xs:
        case Nil{}:
          match a:
        case h <> r:
          match ps:
            case Nil{}:
              match a:
                case (ah, ar):
                  (lv2h_ok(False{}, h, ah), lv2s_ok(u, r, Nil{}, ar))
            case p <> q:
              match a:
                case (ah, ar):
                  (lv2h_ok(p, h, ah), lv2s_ok(u, r, q, ar))

def lvfin_ok(ins: List<&2, M.Ch>, outs: List<&2, M.Ch>, t: Nat, r: List<&2, Bool> & M.Hs, a: AD(t, ins), ao: Ck.AO(outs))
  -> Inv2(S.lv.fin(M.Dev{}, ins, outs, t, r)):
  match r:
    case (ps, hs):
      (lv2s_ok(t, ins, ps, a), ao)

# The system
# ----------

def ent_ok(hs: M.Hs, +k: Nat, +t: Nat, +ins: List<&2, M.Ch>, +outs: List<&2, M.Ch>, i: Inv2(M.Sys{M.Host{}, ins, outs, hs}),
  ok: S.Ok(M.Sys{M.Host{}, ins, outs, hs}, S.Ent{k, t})) -> Inv2(S.step(M.Sys{M.Host{}, ins, outs, hs}, S.Ent{k, t})):
  match hs:
    case M.Hs{pfm, turns, gkey, keys, at, cur, writes, tw}:
      match at:
        case None{}:
          match i:
            case (ai, ao):
              match ok:
                case (u, x):
                  match x:
                    case (qs, le):
                      match qs:
                        case (qi, qo):
                          (en2s_ok(t, ins, qi, ai, le), ao)
        case Some{j}:
          match i:
            case (ai, ao):
              match ok:
                case (u, x):
                  match x:
                    case (qs, le):
                      match qs:
                        case (qi, qo):
                          (en2s_ok(t, ins, qi, ai, le), ao)

def dwr_ok(hs: M.Hs, +ins: List<&2, M.Ch>, +outs: List<&2, M.Ch>, +c: Nat, +v: Nat, +m: Bool, i: Inv2(M.Sys{M.Dev{}, ins, outs, hs}),
  ok: S.Ok(M.Sys{M.Dev{}, ins, outs, hs}, S.DWr{c, v, m})) -> Inv2(S.step(M.Sys{M.Dev{}, ins, outs, hs}, S.DWr{c, v, m})):
  match hs:
    case M.Hs{pfm, turns, gkey, keys, at, cur, writes, +tw}:
      match i:
        case (a, ao):
          match ok:
            case (u, x):
              match x:
                case (lt, mo):
                  (dw2_ok(tw, ins, c, v, m, mo, a), ao)

def bmp_ok(hs: M.Hs, +ins: List<&2, M.Ch>, +m: Nat, +outs: List<&2, M.Ch>, i: Inv2(M.Sys{M.Dev{}, ins, outs, hs}),
  ok: S.Ok(M.Sys{M.Dev{}, ins, outs, hs}, S.Bmp{m})) -> Inv2(S.step(M.Sys{M.Dev{}, ins, outs, hs}, S.Bmp{m})):
  match hs:
    case M.Hs{pfm, turns, gkey, keys, at, cur, writes, +tw}:
      match i:
        case (a, ao):
          rs2_ok(tw, ins, m, outs, ok, a, ao)

def inv_step(s: M.Sys, e: S.Ev, i: Inv2(s), ok: S.Ok(s, e)) -> Inv2(S.step(s, e)):
  match s:
    case M.Sys{ph, +ins, +outs, +hs}:
      match ph:
        case M.Host{}:
          match e:
            case S.Rd{+c}:
              match i:
                case (ai, ao):
                  (P.upd_i_ok(ins, c, M.CRd{}, M.Host{}, Unit{}, ai), P.upd_o_ok(M.len(ins), c, M.CRd{}, outs, Unit{}, ao))
            case S.Wr{+c, +v}:
              match i:
                case (ai, ao):
                  (P.upd_i_ok(ins, c, M.CWr{v}, M.Host{}, Unit{}, ai), P.upd_o_ok(M.len(ins), c, M.CWr{v}, outs, Unit{}, ao))
            case S.Stp{+c, +k}:
              match i:
                case (ai, ao):
                  (P.upd_i_ok(ins, c, M.CSt{k}, M.Host{}, Unit{}, ai), P.upd_o_ok(M.len(ins), c, M.CSt{k}, outs, Unit{}, ao))
            case S.DWr{c, v, m}:
              match ok:
                case (u, x):
                  match u:
            case S.Ent{+k, +t}:
              ent_ok(hs, k, t, ins, outs, i, ok)
            case S.Bmp{+m}:
              match i:
                case (ai, ao):
                  P.rs_ok(M.Host{}, ins, m, outs, ok, ai, ao)
            case S.Lv{}:
              match ok:
        case M.Dev{}:
          match e:
            case S.Rd{c}:
              match ok:
            case S.Wr{c, v}:
              match ok:
            case S.Stp{c, k}:
              match ok:
            case S.DWr{+c, +v, +m}:
              dwr_ok(hs, ins, outs, c, v, m, i, ok)
            case S.Ent{k, t}:
              match ok:
                case (u, x):
                  match u:
            case S.Bmp{+m}:
              bmp_ok(hs, ins, m, outs, i, ok)
            case S.Lv{}:
              match i:
                case (a, ao):
                  lvfin_ok(ins, outs, S.Hs.tw(hs), M.lv_hs(M.len(ins), Nat.add(M.len(ins), M.len(outs)), hs), a, ao)

def inv_run(es: List<&2, S.Ev>, +s: M.Sys, i: Inv2(s), v: S.Valid(es, s)) -> Inv2(S.run(es, s)):
  match es:
    case Nil{}:
      i
    case +e <> t:
      match v:
        case (ok, vt):
          inv_run(t, S.step(s, e), inv_step(s, e, i, ok), vt)

def inv_trace(+n0: Nat, +m0: Nat, +pfm: Nat, es: List<&2, S.Ev>, v: S.Valid(es, M.init(n0, m0, pfm))) -> Inv2(S.run(es, M.init(n0, m0, pfm))):
  inv_run(es, M.init(n0, m0, pfm), P.inv_init(n0, m0, pfm), v)

# The laws, off Inv2
# ------------------

def ad_ai(t: Nat, xs: List<&2, M.Ch>, a: AD(t, xs)) -> Ck.AI(M.Dev{}, xs):
  match t:
    case 0n:
      a
    case 1n+u:
      match xs:
        case Nil{}:
          match a:
        case h <> r:
          match a:
            case (ah, ar):
              match ah:
                case (cd, c):
                  (cd, ad_ai(u, r, ar))

# stage 1's invariant
def to_inv(s: M.Sys, i: Inv2(s)) -> Ck.Inv(s):
  match s:
    case M.Sys{ph, ins, outs, hs}:
      match ph:
        case M.Host{}:
          i
        case M.Dev{}:
          match i:
            case (a, ao):
              (ad_ai(S.Hs.tw(hs), ins, a), ao)

def uc(t: Nat, xs: List<&2, M.Ch>, a: AD(t, xs)) -> S.UCs(t, xs):
  match t:
    case 0n:
      Unit{}
    case 1n+u:
      match xs:
        case Nil{}:
          Unit{}
        case h <> r:
          match a:
            case (ah, ar):
              match ah:
                case (cd, c):
                  (c, uc(u, r, ar))

def l5_of(s: M.Sys, i: Inv2(s)) -> S.L5(s):
  match s:
    case M.Sys{ph, ins, outs, hs}:
      match ph:
        case M.Host{}:
          Unit{}
        case M.Dev{}:
          match i:
            case (a, ao):
              uc(S.Hs.tw(hs), ins, a)

def k0_of(s: M.Sys, i: Inv2(s), +k: Nat, +t: Nat, ok: S.Ok(s, S.Ent{k, t})) -> S.K0(S.step(s, S.Ent{k, t})):
  match s:
    case M.Sys{ph, +ins, outs, hs}:
      match ph:
        case M.Host{}:
          match i:
            case (ai, ao):
              match ok:
                case (u, x):
                  match x:
                    case (qs, le):
                      match qs:
                        case (qi, qo):
                          en2s_k0(ins, qi, ai)
        case M.Dev{}:
          match ok:
            case (u, x):
              match u:

def Laws2.s2_l1_read_fresh(n0, m0, pfm, es, v):
  P.l1_of(S.run(es, M.init(n0, m0, pfm)), to_inv(S.run(es, M.init(n0, m0, pfm)), inv_trace(n0, m0, pfm, es, v)))

def Laws2.s2_l2_no_lost_write(n0, m0, pfm, es, v):
  P.l2_of(S.run(es, M.init(n0, m0, pfm)), to_inv(S.run(es, M.init(n0, m0, pfm)), inv_trace(n0, m0, pfm, es, v)))

def Laws2.s2_l3_prefetch_current(n0, m0, pfm, es, v):
  P.l3_of(S.run(es, M.init(n0, m0, pfm)), to_inv(S.run(es, M.init(n0, m0, pfm)), inv_trace(n0, m0, pfm, es, v)))

def Laws2.s2_l4_used_once(n0, m0, pfm, es, v):
  P.l4_of(S.run(es, M.init(n0, m0, pfm)), to_inv(S.run(es, M.init(n0, m0, pfm)), inv_trace(n0, m0, pfm, es, v)))

def Laws2.s2_l5_unmarked_keepable(n0, m0, pfm, es, v):
  l5_of(S.run(es, M.init(n0, m0, pfm)), inv_trace(n0, m0, pfm, es, v))

def Laws2.s2_k0_enter(n0, m0, pfm, es, v, k, t, ok):
  k0_of(S.run(es, M.init(n0, m0, pfm)), inv_trace(n0, m0, pfm, es, v), k, t, ok)
