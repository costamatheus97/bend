# ReachModel -- the lane bound: with budget + RC_SLACK fuel a lane
# always ends (ReachLaws.bend states it, ReachProof.bend cites this).
# The invariant, n steps so far and B the budget: at a pop the stack's
# k words give k + n <= 305 + B; in a node's words (j left) or a leaf's,
# j + n <= 257 + B; at a sealed cell n <= B; the stack stays <= 48. A
# pop past the budget enters nothing; one under it enters a node at
# n <= B, 1 + B through a sealed cell, of at most 2^RC_PIECE words
# after the split; then at most RC_STACK = 48 pops. Every step keeps it
# or ends the lane, so 305 + B < 306 + B fuel is enough.
import Base
import ./ReachModel.bend as M

# Nat and LE
# ----------
def add_succ(+a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def le_trans(+a: Nat, +b: Nat, +c: Nat, ab: M.LE(a, b), bc: M.LE(b, c)) -> M.LE(a, c):
  match a b c:
    case 0n _ _:
      Unit{}
    case 1n+p 0n _:
      Empty.absurd(M.LE(1n+p, c), ab)
    case 1n+p 1n+q 0n:
      Empty.absurd(M.LE(1n+p, 0n), bc)
    case 1n+p 1n+q 1n+r:
      le_trans(p, q, r, ab, bc)

def le_prefix(+a: Nat, +b: Nat) -> M.LE(b, Nat.add(a, b)):
  match b:
    case 0n:
      Unit{}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(a, 1n+p), 1n+Nat.add(a, p), add_succ(a, p)) : M.LE(1n+p, _)
      le_prefix(a, p)

def le_succ(+a: Nat, +b: Nat, e: M.LE(a, b)) -> M.LE(a, 1n+b):
  match a b:
    case 0n _:
      Unit{}
    case 1n+p 0n:
      Empty.absurd(M.LE(1n+p, 1n), e)
    case 1n+p 1n+q:
      le_succ(p, q, e)

def no_lt_self(+a: Nat, e: M.LE(1n+a, a)) -> Empty:
  match a:
    case 0n:
      e
    case 1n+p:
      no_lt_self(p, e)

# a + c <= b + c, from a <= b (on the first argument, where add recurses)
def le_add_r(+a: Nat, +b: Nat, +c: Nat, e: M.LE(a, b)) -> M.LE(Nat.add(a, c), Nat.add(b, c)):
  match a b:
    case 0n _:
      le_prefix(b, c)
    case 1n+p 0n:
      Empty.absurd(M.LE(Nat.add(1n+p, c), c), e)
    case 1n+p 1n+q:
      le_add_r(p, q, c, e)

# a Bool with what it means
def Refl(c: Bool, A: Type, B: Type) -> Type:
  match c:
    case True{}:
      A
    case False{}:
      B

def refl_lt(+a: Nat, +b: Nat) -> Refl(Nat.is_lt(a, b), M.LE(1n+a, b), M.LE(b, a)):
  match a b:
    case 0n 0n:
      Unit{}
    case 0n 1n+q:
      Unit{}
    case 1n+p 0n:
      Unit{}
    case 1n+p 1n+q:
      refl_lt(p, q)

def refl_le(+a: Nat, +b: Nat) -> Refl(Nat.is_le(a, b), M.LE(a, b), M.LE(1n+b, a)):
  match a b:
    case 0n 0n:
      Unit{}
    case 0n 1n+q:
      Unit{}
    case 1n+p 0n:
      Unit{}
    case 1n+p 1n+q:
      refl_le(p, q)

# k <= 48 and n <= 257 + B: k + n <= 305 + B
def pop_arith(+k: Nat, +n: Nat, +B: Nat, hk: M.LE(k, 48n), hn: M.LE(n, Nat.add(257n, B))) -> M.LE(Nat.add(k, n), Nat.add(305n, B)):
  le_trans(Nat.add(k, n), Nat.add(48n, n), Nat.add(305n, B), le_add_r(k, 48n, n, hk), hn)

# j <= 256 and n <= 1 + B: j + n <= 257 + B
def kids_arith(+j: Nat, +n: Nat, +B: Nat, hj: M.LE(j, 256n), hn: M.LE(n, 1n+B)) -> M.LE(Nat.add(j, n), Nat.add(257n, B)):
  le_trans(Nat.add(j, n), Nat.add(256n, n), Nat.add(257n, B), le_add_r(j, 256n, n, hj), hn)

# n <= 1 + B: n <= 257 + B
def up257(+n: Nat, +B: Nat, hn: M.LE(n, 1n+B)) -> M.LE(n, Nat.add(257n, B)):
  le_trans(n, 1n+B, Nat.add(257n, B), hn, le_prefix(256n, 1n+B))

def add_zero(+a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def add_comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, add_zero(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), add_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# The invariant
# -------------

def st_of(r: M.R) -> List<&2, M.T>:
  match r:
    case M.R{st, acc, marks, seen}:
      st

# the words on the stack
def ks(r: M.R) -> Nat:
  List.length(&2, M.T, st_of(r))

# n steps so far, B the budget: a pop leaves at most 305 + B - n steps
# (the stack's words), a node's words at most 257 + B - n with its j
# left, a sealed cell is entered at most at B
def Inv.m(+B: Nat, +n: Nat, -len: Nat, m: M.Mode<len>, +k: Nat) -> Type:
  match m:
    case M.Pop{}:
      (M.LE(k, 48n) & M.LE(Nat.add(k, n), Nat.add(305n, B)))
    case M.Kids{i, j, e}:
      (M.LE(k, 48n) & M.LE(Nat.add(j, n), Nat.add(257n, B)))
    case M.Leaf{j}:
      (M.LE(k, 48n) & M.LE(Nat.add(j, n), Nat.add(257n, B)))
    case M.Cell{t, i, e}:
      (M.LE(k, 48n) & M.LE(n, B))

def Inv(+B: Nat, +n: Nat, -len: Nat, s: M.S<len>) -> Type:
  match s:
    case M.S{mode, r, last}:
      Inv.m(B, n, len, mode, ks(r))

# the step did something (it was not idle)
def live(k: M.K) -> Type:
  match k:
    case M.Idle{}:
      Empty
    case M.Popd{}:
      Unit
    case M.Read{}:
      Unit
    case M.Walk{}:
      Unit

def Ok(+B: Nat, +n: Nat, -len: Nat, +s: M.S<len>) -> Type:
  (Inv(B, n, len, s) & live(M.S.last(len, s)))

def tr48(+a: Nat, +b: Nat, e: {a == b : Nat}, h: M.LE(a, 48n)) -> M.LE(b, 48n):
  %e : M.LE(_, 48n)
  h

# The stack's size through each change
# ------------------------------------

def ks_bad(t: M.T, +r: M.R) -> {ks(r) == ks(M.r_bad(t, r)) : Nat}:
  match r:
    case M.R{st, acc, marks, seen}:
      match acc:
        case M.Acc{out, nout, bad, fbad, split, hits}:
          {==}

def ks_hit(+r: M.R) -> {ks(r) == ks(M.r_hit(r)) : Nat}:
  match r:
    case M.R{st, acc, marks, seen}:
      match acc:
        case M.Acc{out, nout, bad, fbad, split, hits}:
          {==}

def ks_spill(t: M.T, +r: M.R) -> {ks(r) == ks(M.r_spill(t, r)) : Nat}:
  match r:
    case M.R{st, acc, marks, seen}:
      match acc:
        case M.Acc{out, nout, bad, fbad, split, hits}:
          {==}

def ks_split(+r: M.R) -> {ks(r) == ks(M.r_split(r)) : Nat}:
  match r:
    case M.R{st, acc, marks, seen}:
      match acc:
        case M.Acc{out, nout, bad, fbad, split, hits}:
          {==}

def ks_see(+i: Nat, +r: M.R) -> {ks(r) == ks(M.r_see(i, r)) : Nat}:
  match r:
    case M.R{st, acc, marks, seen}:
      {==}

def ks_mark.fin(+cx: M.Cx, +l: Nat, +m: Nat, ok: Bool, +r: M.R) -> {ks(r) == ks(M.r_mark.fin(cx, l, m, ok, r)) : Nat}:
  match ok:
    case False{}:
      {==}
    case True{}:
      match r:
        case M.R{st, acc, marks, seen}:
          {==}

def ks_mark(+cx: M.Cx, +l: Nat, +m: Nat, +r: M.R) -> {ks(r) == ks(M.r_mark(cx, l, m, r)) : Nat}:
  ks_mark.fin(cx, l, m, Bool.and(Nat.is_le(M.Cx.lo(cx), l), Nat.is_le(Nat.add(l, m), M.Cx.hi(cx))), r)

def push_k.fin(room: Bool, +st: List<&2, M.T>, ev: Refl(room, M.LE(1n+List.length(&2, M.T, st), 48n), M.LE(48n, List.length(&2, M.T, st))),
  t: M.T, acc: M.Acc, marks: List<&2, Nat>, seen: List<&2, Nat>, h: M.LE(List.length(&2, M.T, st), 48n))
  -> M.LE(ks(M.r_push.fin(room, t, st, acc, marks, seen)), 48n):
  match room:
    case True{}:
      ev
    case False{}:
      match acc:
        case M.Acc{out, nout, bad, fbad, split, hits}:
          h

def push_k(t: M.T, +r: M.R, h: M.LE(ks(r), 48n)) -> M.LE(ks(M.r_push(t, r)), 48n):
  match r:
    case M.R{+st, acc, marks, seen}:
      push_k.fin(Nat.is_lt(List.length(&2, M.T, st), 48n), st, refl_lt(List.length(&2, M.T, st), 48n), t, acc, marks, seen, h)

def kid_k.fin(leaf: Bool, t: M.T, +r: M.R, h: M.LE(ks(r), 48n)) -> M.LE(ks(M.r_kid.fin(leaf, t, r)), 48n):
  match leaf:
    case True{}:
      h
    case False{}:
      push_k(t, r, h)

def kid_k(+off: Nat, +t: M.T, +r: M.R, h: M.LE(ks(r), 48n)) -> M.LE(ks(M.r_kid(off, t, r)), 48n):
  kid_k.fin(M.triv(off, t), t, r, h)

# The steps keep the invariant
# ----------------------------

def pop_ok(+B: Nat, +n: Nat, -len: Nat, +x: M.R, +last: M.K, +hk: M.LE(ks(x), 48n), hn: M.LE(n, Nat.add(257n, B)), lv: live(last))
  -> Ok(B, n, len, M.S{M.Pop{}, x, last}):
  ((hk, pop_arith(ks(x), n, B, hk, hn)), lv)

# the z loop: from a pop (n <= B) or a sealed cell's target (n <= 1 + B)
def entry_words_ok(+heap: M.Heap, +cx: M.Cx, +t: M.T, +k: Nat, kids: Bool,
  +e: M.LE(1n+Nat.add(k, M.rel(cx, t)), M.hl(heap)), +x: M.R, +last: M.K, +n: Nat, +B: Nat,
  hj: M.LE(1n+k, 256n), hB: M.LE(n, 1n+B), hk: M.LE(ks(x), 48n), lv: live(last))
  -> Ok(B, n, M.hl(heap), M.entry.words(heap, cx, t, k, kids, e, x, last)):
  match kids:
    case True{}:
      ((hk, kids_arith(1n+k, n, B, hj, hB)), lv)
    case False{}:
      ((hk, kids_arith(1n+k, n, B, hj, hB)), lv)

def entry_fit_ok(+heap: M.Heap, +cx: M.Cx, +t: M.T, +k: Nat, kids: Bool,
  +e: M.LE(1n+Nat.add(k, M.rel(cx, t)), M.hl(heap)), big: Bool, ev: Refl(big, M.LE(257n, 1n+k), M.LE(1n+k, 256n)),
  +r: M.R, +last: M.K, +n: Nat, +B: Nat, hB: M.LE(n, 1n+B), +hk: M.LE(ks(r), 48n), lv: live(last))
  -> Ok(B, n, M.hl(heap), M.entry.fit(heap, cx, t, k, kids, e, big, r, last)):
  match big:
    case True{}:
      +in1 = M.r_push(M.half(t, Nat.add(M.tloc(t), Nat.div(1n+k, 2n))), r)
      +in2 = M.r_push(M.half(t, M.tloc(t)), in1)
      pop_ok(B, n, M.hl(heap), M.r_split(in2), last,
        tr48(ks(in2), ks(M.r_split(in2)), ks_split(in2),
          push_k(M.half(t, M.tloc(t)), in1, push_k(M.half(t, Nat.add(M.tloc(t), Nat.div(1n+k, 2n))), r, hk))),
        up257(n, B, hB), lv)
    case False{}:
      entry_words_ok(heap, cx, t, k, kids, e, M.r_mark(cx, M.tloc(t), 1n+k, r), last, n, B, ev, hB,
        tr48(ks(r), ks(M.r_mark(cx, M.tloc(t), 1n+k, r)), ks_mark(cx, M.tloc(t), 1n+k, r), hk), lv)

def entry_some_ok(+heap: M.Heap, +cx: M.Cx, +t: M.T, +k: Nat, kids: Bool,
  c: Or(M.LE(1n+Nat.add(k, M.rel(cx, t)), M.hl(heap)), M.LE(M.hl(heap), Nat.add(k, M.rel(cx, t)))),
  +r: M.R, +last: M.K, +n: Nat, +B: Nat, +hB: M.LE(n, 1n+B), +hk: M.LE(ks(r), 48n), lv: live(last))
  -> Ok(B, n, M.hl(heap), M.entry.some(heap, cx, t, k, kids, c, r, last)):
  match c:
    case Inl{e}:
      entry_fit_ok(heap, cx, t, k, kids, e, Nat.is_lt(M.rc_piece(), 1n+k), refl_lt(M.rc_piece(), 1n+k), r, last, n, B, hB, hk, lv)
    case Inr{e}:
      pop_ok(B, n, M.hl(heap), M.r_bad(t, r), last, tr48(ks(r), ks(M.r_bad(t, r)), ks_bad(t, r), hk), up257(n, B, hB), lv)

def entry_none_ok(+heap: M.Heap, +cx: M.Cx, +t: M.T,
  c: Or(M.LE(1n+M.rel(cx, t), M.hl(heap)), M.LE(M.hl(heap), M.rel(cx, t))),
  +r: M.R, +last: M.K, +n: Nat, +B: Nat, +hB: M.LE(n, 1n+B), +hk: M.LE(ks(r), 48n), lv: live(last))
  -> Ok(B, n, M.hl(heap), M.entry.none(heap, cx, t, c, r, last)):
  match c:
    case Inl{e}:
      pop_ok(B, n, M.hl(heap), M.r_mark(cx, M.tloc(t), 1n, r), last,
        tr48(ks(r), ks(M.r_mark(cx, M.tloc(t), 1n, r)), ks_mark(cx, M.tloc(t), 1n, r), hk), up257(n, B, hB), lv)
    case Inr{e}:
      pop_ok(B, n, M.hl(heap), M.r_bad(t, r), last, tr48(ks(r), ks(M.r_bad(t, r)), ks_bad(t, r), hk), up257(n, B, hB), lv)

def entry_n_ok(+heap: M.Heap, +cx: M.Cx, +t: M.T, sz: Nat, kids: Bool, +r: M.R, +last: M.K, +n: Nat, +B: Nat,
  +hB: M.LE(n, 1n+B), +hk: M.LE(ks(r), 48n), lv: live(last))
  -> Ok(B, n, M.hl(heap), M.entry.n(heap, cx, t, sz, kids, r, last)):
  match sz:
    case 0n:
      entry_none_ok(heap, cx, t, M.lt_dec(M.rel(cx, t), M.hl(heap)), r, last, n, B, hB, hk, lv)
    case 1n++k:
      entry_some_ok(heap, cx, t, k, kids, M.lt_dec(Nat.add(k, M.rel(cx, t)), M.hl(heap)), r, last, n, B, hB, hk, lv)

def entry_span_ok(+heap: M.Heap, +cx: M.Cx, +t: M.T, sp: M.Sp, +r: M.R, +last: M.K, +n: Nat, +B: Nat,
  +hB: M.LE(n, 1n+B), +hk: M.LE(ks(r), 48n), lv: live(last))
  -> Ok(B, n, M.hl(heap), M.entry.span(heap, cx, t, sp, r, last)):
  match sp:
    case M.Bad{}:
      pop_ok(B, n, M.hl(heap), M.r_bad(t, r), last, tr48(ks(r), ks(M.r_bad(t, r)), ks_bad(t, r), hk), up257(n, B, hB), lv)
    case M.Sp{sz, kids}:
      entry_n_ok(heap, cx, t, sz, kids, r, last, n, B, hB, hk, lv)

def entry_cell_ok(+heap: M.Heap, +cx: M.Cx, +t: M.T, +i: Nat, c: Or(M.LE(1n+i, M.hl(heap)), M.LE(M.hl(heap), i)),
  +r: M.R, +last: M.K, +n: Nat, +B: Nat, +hB: M.LE(n, B), +hk: M.LE(ks(r), 48n), lv: live(last))
  -> Ok(B, n, M.hl(heap), M.entry.cell(heap, cx, t, i, c, r, last)):
  match c:
    case Inl{e}:
      ((tr48(ks(r), ks(M.r_mark(cx, M.tloc(t), 1n, r)), ks_mark(cx, M.tloc(t), 1n, r), hk), hB), lv)
    case Inr{e}:
      pop_ok(B, n, M.hl(heap), M.r_bad(t, r), last, tr48(ks(r), ks(M.r_bad(t, r)), ks_bad(t, r), hk),
        up257(n, B, le_succ(n, B, hB)), lv)

def entry_go_ok(+heap: M.Heap, +cx: M.Cx, rfc: Bool, +t: M.T, +r: M.R, +last: M.K, +n: Nat, +B: Nat,
  +hB: M.LE(n, B), +hk: M.LE(ks(r), 48n), lv: live(last))
  -> Ok(B, n, M.hl(heap), M.entry.go(heap, cx, rfc, t, r, last)):
  match rfc:
    case True{}:
      entry_cell_ok(heap, cx, t, M.rel(cx, t), M.lt_dec(M.rel(cx, t), M.hl(heap)), r, last, n, B, hB, hk, lv)
    case False{}:
      entry_span_ok(heap, cx, t, M.span(M.Cx.ctab(cx), M.Cx.ftab(cx), t), r, last, n, B, le_succ(n, B, hB), hk, lv)

def entry_ok(+heap: M.Heap, +cx: M.Cx, +t: M.T, +r: M.R, +last: M.K, +n: Nat, +B: Nat,
  +hB: M.LE(n, B), +hk: M.LE(ks(r), 48n), lv: live(last))
  -> Ok(B, n, M.hl(heap), M.entry(heap, cx, t, r, last)):
  match t:
    case M.T{+rfc, +tag, +aux, +loc}:
      entry_go_ok(heap, cx, rfc, M.T{rfc, tag, aux, loc}, r, last, n, B, hB, hk, lv)

# The pops
# --------

# j + 1 + n from 1 + j + n (add recurses on its first argument)
def shift(+j: Nat, +n: Nat, +C: Nat, h: M.LE(1n+Nat.add(j, n), C)) -> M.LE(Nat.add(j, 1n+n), C):
  %Equal.sym(Nat, Nat.add(j, 1n+n), 1n+Nat.add(j, n), add_succ(j, n)) : M.LE(_, C)
  h

def shift2(+j: Nat, +n: Nat, +C: Nat, h: M.LE(C, 1n+Nat.add(j, n))) -> M.LE(C, Nat.add(j, 1n+n)):
  %Equal.sym(Nat, Nat.add(j, 1n+n), 1n+Nat.add(j, n), add_succ(j, n)) : M.LE(C, _)
  h

def trs(+a: Nat, +b: Nat, e: {a == b : Nat}, +n: Nat, +C: Nat, h: M.LE(Nat.add(a, n), C)) -> M.LE(Nat.add(b, n), C):
  %e : M.LE(Nat.add(_, n), C)
  h

# a pop that ends the word: the stack one shorter (k2 words), a step more
def pop_next(+k: Nat, +k2: Nat, +q: {k == k2 : Nat}, +n: Nat, +B: Nat, +hk: M.LE(1n+k, 48n), hn: M.LE(1n+Nat.add(k, n), Nat.add(305n, B)))
  -> (M.LE(k2, 48n) & M.LE(Nat.add(k2, 1n+n), Nat.add(305n, B))):
  (tr48(k, k2, q, M.le_pred(k, 48n, hk)), trs(k, k2, q, 1n+n, Nat.add(305n, B), shift(k, n, Nat.add(305n, B), hn)))

# r: the stack without the popped word t; n steps before the pop
def pop_over_ok(+heap: M.Heap, +cx: M.Cx, +B: Nat, +n: Nat, over: Bool, ev: Refl(over, M.LE(B, n), M.LE(1n+n, B)),
  +t: M.T, +r: M.R, +hk: M.LE(1n+ks(r), 48n), hn: M.LE(1n+Nat.add(ks(r), n), Nat.add(305n, B)))
  -> Ok(B, 1n+n, M.hl(heap), M.pop.over(heap, cx, over, t, r)):
  match over:
    case True{}:
      (pop_next(ks(r), ks(M.r_spill(t, r)), ks_spill(t, r), n, B, hk, hn), Unit{})
    case False{}:
      entry_ok(heap, cx, t, r, M.Popd{}, 1n+n, B, ev, M.le_pred(ks(r), 48n, hk), Unit{})

def pop_arg_ok(+heap: M.Heap, +cx: M.Cx, +B: Nat, +n: Nat, arg: Bool,
  +t: M.T, +r: M.R, +hk: M.LE(1n+ks(r), 48n), hn: M.LE(1n+Nat.add(ks(r), n), Nat.add(305n, B)))
  -> Ok(B, 1n+n, M.hl(heap), M.pop.arg(heap, cx, B, n, arg, t, r)):
  match arg:
    case True{}:
      (pop_next(ks(r), ks(M.r_hit(r)), ks_hit(r), n, B, hk, hn), Unit{})
    case False{}:
      pop_over_ok(heap, cx, B, n, Nat.is_le(B, n), refl_le(B, n), t, r, hk, hn)

def pop_leaf_ok(+heap: M.Heap, +cx: M.Cx, +B: Nat, +n: Nat, leaf: Bool,
  +t: M.T, +r: M.R, +hk: M.LE(1n+ks(r), 48n), hn: M.LE(1n+Nat.add(ks(r), n), Nat.add(305n, B)))
  -> Ok(B, 1n+n, M.hl(heap), M.pop.leaf(heap, cx, B, n, leaf, t, r)):
  match leaf:
    case True{}:
      (pop_next(ks(r), ks(r), {==}, n, B, hk, hn), Unit{})
    case False{}:
      pop_arg_ok(heap, cx, B, n, Bool.and(Bool.not(M.Cx.follow(cx)), M.tmem(t, M.Cx.args(cx))), t, r, hk, hn)

# The sealed cells
# ----------------

def cell_to_fin_ok(+heap: M.Heap, +cx: M.Cx, +B: Nat, +n: Nat, leaf: Bool, +tag: Nat, +aux: Nat, +loc: Nat,
  +r: M.R, +hk: M.LE(ks(r), 48n), +hB: M.LE(n, B))
  -> Ok(B, 1n+n, M.hl(heap), M.cell.to.fin(heap, cx, leaf, M.T{False{}, tag, aux, loc}, r)):
  match leaf:
    case True{}:
      pop_ok(B, 1n+n, M.hl(heap), r, M.Read{}, hk, up257(1n+n, B, hB), Unit{})
    case False{}:
      entry_span_ok(heap, cx, M.T{False{}, tag, aux, loc}, M.span(M.Cx.ctab(cx), M.Cx.ftab(cx), M.T{False{}, tag, aux, loc}),
        r, M.Read{}, 1n+n, B, hB, hk, Unit{})

def cell_fin_ok(+heap: M.Heap, +cx: M.Cx, +B: Nat, +n: Nat, go: Bool, t: M.T, +i: Nat, +e: M.LE(1n+i, M.hl(heap)),
  +r: M.R, +hk: M.LE(ks(r), 48n), +hB: M.LE(n, B))
  -> Ok(B, 1n+n, M.hl(heap), M.cell.fin(heap, cx, go, t, i, e, r)):
  match go:
    case False{}:
      pop_ok(B, 1n+n, M.hl(heap), r, M.Walk{}, hk, up257(1n+n, B, hB), Unit{})
    case True{}:
      match t:
        case M.T{rfc, +tag, +aux, loc}:
          cell_to_fin_ok(heap, cx, B, n, M.triv(M.Cx.off(cx), M.T{False{}, tag, aux, M.cell(M.Heap.read(heap, i, e))}),
            tag, aux, M.cell(M.Heap.read(heap, i, e)), M.r_see(i, r),
            tr48(ks(r), ks(M.r_see(i, r)), ks_see(i, r), hk), hB)

# The fuel
# --------

def IsT(b: Bool) -> Data:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def ist_eq(b: Bool, d: IsT(b)) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      match d:

# a live step counts one
def tally_live(+c: M.Ctr, +k: M.K, lv: live(k)) -> {1n+M.Ctr.steps(c) == M.Ctr.steps(M.tally(c, k)) : Nat}:
  match c:
    case M.Ctr{p, r, w, i}:
      match k:
        case M.Idle{}:
          match lv:
        case M.Popd{}:
          {==}
        case M.Read{}:
          %Equal.sym(Nat, Nat.add(p, 1n+Nat.add(r, w)), 1n+Nat.add(p, Nat.add(r, w)), add_succ(p, Nat.add(r, w))) : {1n+Nat.add(p, Nat.add(r, w)) == _ : Nat}
          {==}
        case M.Walk{}:
          %Equal.sym(Nat, Nat.add(r, 1n+w), 1n+Nat.add(r, w), add_succ(r, w)) : {1n+Nat.add(p, Nat.add(r, w)) == Nat.add(p, _) : Nat}
          %Equal.sym(Nat, Nat.add(p, 1n+Nat.add(r, w)), 1n+Nat.add(p, Nat.add(r, w)), add_succ(p, Nat.add(r, w))) : {1n+Nat.add(p, Nat.add(r, w)) == _ : Nat}
          {==}

# n steps so far and F fuel left: the invariant with 305 + B < F + n,
# or the lane is done
def Pn(+B: Nat, +F: Nat, +n: Nat, -len: Nat, +s: M.S<len>) -> Type:
  Or((Inv(B, n, len, s) & M.LE(1n+Nat.add(305n, B), Nat.add(F, n))), IsT(M.S.done(len, s)))

def mk_next(+B: Nat, +f: Nat, +c: M.Ctr, -len: Nat, +s2: M.S<len>, ok: Ok(B, 1n+M.Ctr.steps(c), len, s2),
  h: M.LE(1n+Nat.add(305n, B), 1n+Nat.add(f, M.Ctr.steps(c))))
  -> Pn(B, f, M.Ctr.steps(M.tally(c, M.S.last(len, s2))), len, s2):
  match ok:
    case (inv, lv):
      %tally_live(c, M.S.last(len, s2), lv) : Pn(B, f, _, len, s2)
      Inl{(inv, shift2(f, M.Ctr.steps(c), 1n+Nat.add(305n, B), h))}

# the stack r, n steps: the pop keeps the invariant or the lane is done
def pop_P(+heap: M.Heap, +cx: M.Cx, +B: Nat, +f: Nat, +c: M.Ctr, r: M.R, +hk: M.LE(ks(r), 48n),
  hs: M.LE(Nat.add(ks(r), M.Ctr.steps(c)), Nat.add(305n, B)), h: M.LE(1n+Nat.add(305n, B), 1n+Nat.add(f, M.Ctr.steps(c))))
  -> Pn(B, f, M.Ctr.steps(M.tally(c, M.S.last(M.hl(heap), M.pop.step(heap, cx, B, M.Ctr.steps(c), r)))), M.hl(heap), M.pop.step(heap, cx, B, M.Ctr.steps(c), r)):
  match r:
    case M.R{st, +acc, +marks, +seen}:
      match st:
        case Nil{}:
          Inr{Unit{}}
        case +w <> +rest:
          mk_next(B, f, c, M.hl(heap), M.pop.leaf(heap, cx, B, M.Ctr.steps(c), M.triv(M.Cx.off(cx), w), w, M.R{rest, acc, marks, seen}),
            pop_leaf_ok(heap, cx, B, M.Ctr.steps(c), M.triv(M.Cx.off(cx), w), w, M.R{rest, acc, marks, seen}, hk, hs), h)

# a node's words or a leaf's done: the pop, from j = 0
def pop0(+heap: M.Heap, +cx: M.Cx, +B: Nat, +f: Nat, +c: M.Ctr, +r: M.R, +hk: M.LE(ks(r), 48n),
  hj: M.LE(M.Ctr.steps(c), Nat.add(257n, B)), h: M.LE(1n+Nat.add(305n, B), 1n+Nat.add(f, M.Ctr.steps(c))))
  -> Pn(B, f, M.Ctr.steps(M.tally(c, M.S.last(M.hl(heap), M.pop.step(heap, cx, B, M.Ctr.steps(c), r)))), M.hl(heap), M.pop.step(heap, cx, B, M.Ctr.steps(c), r)):
  pop_P(heap, cx, B, f, c, r, hk, pop_arith(ks(r), M.Ctr.steps(c), B, hk, hj), h)

# one step: the invariant a step on, or the lane done
def step_ok(+heap: M.Heap, +cx: M.Cx, +B: Nat, +f: Nat, s: M.S<M.hl(heap)>, +c: M.Ctr,
  inv: Inv(B, M.Ctr.steps(c), M.hl(heap), s), h: M.LE(1n+Nat.add(305n, B), 1n+Nat.add(f, M.Ctr.steps(c))))
  -> Pn(B, f, M.Ctr.steps(M.tally(c, M.S.last(M.hl(heap), M.step(heap, cx, B, M.Ctr.steps(c), s)))), M.hl(heap), M.step(heap, cx, B, M.Ctr.steps(c), s)):
  match s:
    case M.S{mode, +r, last}:
      match mode:
        case M.Pop{}:
          match inv:
            case (hk, hs):
              pop_P(heap, cx, B, f, c, r, hk, hs, h)
        case M.Kids{i, 0n, e}:
          match inv:
            case (hk, hj):
              pop0(heap, cx, B, f, c, r, hk, hj, h)
        case M.Kids{+i, 1n++j, +e}:
          match inv:
            case (hk, hj):
              mk_next(B, f, c, M.hl(heap), M.kids.step(heap, cx, i, j, e, r),
                ((kid_k(M.Cx.off(cx), M.decode(M.Heap.read(heap, Nat.add(j, i), e)), r, hk),
                  shift(j, M.Ctr.steps(c), Nat.add(257n, B), hj)), Unit{}), h)
        case M.Leaf{0n}:
          match inv:
            case (hk, hj):
              pop0(heap, cx, B, f, c, r, hk, hj, h)
        case M.Leaf{1n++j}:
          match inv:
            case (hk, hj):
              mk_next(B, f, c, M.hl(heap), M.S{M.Leaf{j}, r, M.Walk{}},
                ((hk, shift(j, M.Ctr.steps(c), Nat.add(257n, B), hj)), Unit{}), h)
        case M.Cell{+t, +i, +e}:
          match inv:
            case (hk, hB):
              mk_next(B, f, c, M.hl(heap), M.cell.step(heap, cx, t, i, e, r),
                cell_fin_ok(heap, cx, B, M.Ctr.steps(c), Bool.and(M.Cx.follow(cx), Bool.not(M.r_has(i, r))), t, i, e, r, hk, hB), h)

# the invariant bounds the steps: n <= 305 + B
def inv_le(+B: Nat, +n: Nat, -len: Nat, s: M.S<len>, inv: Inv(B, n, len, s)) -> M.LE(n, Nat.add(305n, B)):
  match s:
    case M.S{mode, +r, last}:
      match mode:
        case M.Pop{}:
          match inv:
            case (hk, hs):
              le_trans(n, Nat.add(ks(r), n), Nat.add(305n, B), le_prefix(ks(r), n), hs)
        case M.Kids{i, +j, e}:
          match inv:
            case (hk, hj):
              le_trans(n, Nat.add(j, n), Nat.add(305n, B), le_prefix(j, n),
                le_trans(Nat.add(j, n), Nat.add(257n, B), Nat.add(305n, B), hj, le_add_r(257n, 305n, B, Unit{})))
        case M.Leaf{+j}:
          match inv:
            case (hk, hj):
              le_trans(n, Nat.add(j, n), Nat.add(305n, B), le_prefix(j, n),
                le_trans(Nat.add(j, n), Nat.add(257n, B), Nat.add(305n, B), hj, le_add_r(257n, 305n, B, Unit{})))
        case M.Cell{t, i, e}:
          match inv:
            case (hk, hB):
              le_trans(n, B, Nat.add(305n, B), hB, le_prefix(305n, B))

# no fuel left while the invariant holds: impossible
def no_fuel(+B: Nat, +n: Nat, -len: Nat, +s: M.S<len>, inv: Inv(B, n, len, s), h: M.LE(1n+Nat.add(305n, B), n))
  -> IsT(M.S.done(len, s)):
  Empty.absurd(IsT(M.S.done(len, s)),
    no_lt_self(Nat.add(305n, B), le_trans(1n+Nat.add(305n, B), n, Nat.add(305n, B), h, inv_le(B, n, len, s, inv))))

# a done lane stays done
def done_step(+heap: M.Heap, +cx: M.Cx, +B: Nat, +n: Nat, s: M.S<M.hl(heap)>, d: IsT(M.S.done(M.hl(heap), s)))
  -> IsT(M.S.done(M.hl(heap), M.step(heap, cx, B, n, s))):
  match s:
    case M.S{mode, r, last}:
      match mode:
        case M.Pop{}:
          match r:
            case M.R{st, acc, marks, seen}:
              match st:
                case Nil{}:
                  Unit{}
                case w <> rest:
                  match d:
        case M.Kids{i, 0n, e}:
          match r:
            case M.R{st, acc, marks, seen}:
              match st:
                case Nil{}:
                  Unit{}
                case w <> rest:
                  match d:
        case M.Kids{i, 1n+j, e}:
          match r:
            case M.R{st, acc, marks, seen}:
              match st:
                case Nil{}:
                  match d:
                case w <> rest:
                  match d:
        case M.Leaf{0n}:
          match r:
            case M.R{st, acc, marks, seen}:
              match st:
                case Nil{}:
                  Unit{}
                case w <> rest:
                  match d:
        case M.Leaf{1n+j}:
          match r:
            case M.R{st, acc, marks, seen}:
              match st:
                case Nil{}:
                  match d:
                case w <> rest:
                  match d:
        case M.Cell{t, i, e}:
          match r:
            case M.R{st, acc, marks, seen}:
              match st:
                case Nil{}:
                  match d:
                case w <> rest:
                  match d:

def go_done(+heap: M.Heap, +cx: M.Cx, +B: Nat, F: Nat, +s: M.S<M.hl(heap)>, +c: M.Ctr, d: IsT(M.S.done(M.hl(heap), s)))
  -> IsT(M.S.done(M.hl(heap), M.Lane.s(M.hl(heap), M.go(heap, cx, B, F, s, c)))):
  match F:
    case 0n:
      d
    case 1n+f:
      go_done(heap, cx, B, f, M.step(heap, cx, B, M.Ctr.steps(c), s),
        M.tally(c, M.S.last(M.hl(heap), M.step(heap, cx, B, M.Ctr.steps(c), s))),
        done_step(heap, cx, B, M.Ctr.steps(c), s, d))

# the induction on the fuel
def go_ends(+heap: M.Heap, +cx: M.Cx, +B: Nat, F: Nat, +s: M.S<M.hl(heap)>, +c: M.Ctr, p: Pn(B, F, M.Ctr.steps(c), M.hl(heap), s))
  -> IsT(M.S.done(M.hl(heap), M.Lane.s(M.hl(heap), M.go(heap, cx, B, F, s, c)))):
  match F:
    case 0n:
      match p:
        case Inl{x}:
          match x:
            case (inv, h):
              no_fuel(B, M.Ctr.steps(c), M.hl(heap), s, inv, h)
        case Inr{d}:
          d
    case 1n++f:
      match p:
        case Inl{x}:
          match x:
            case (inv, h):
              go_ends(heap, cx, B, f, M.step(heap, cx, B, M.Ctr.steps(c), s),
                M.tally(c, M.S.last(M.hl(heap), M.step(heap, cx, B, M.Ctr.steps(c), s))),
                step_ok(heap, cx, B, f, s, c, inv, h))
        case Inr{d}:
          go_done(heap, cx, B, 1n+f, s, c, d)

def le_refl(+a: Nat) -> M.LE(a, a):
  match a:
    case 0n:
      Unit{}
    case 1n+p:
      le_refl(p)

# the lane's fuel, budget + 306, against 1 + 305 + budget
def fuel0(+B: Nat) -> M.LE(1n+Nat.add(305n, B), Nat.add(Nat.add(B, 306n), 0n)):
  %Equal.sym(Nat, Nat.add(Nat.add(B, 306n), 0n), Nat.add(B, 306n), add_zero(Nat.add(B, 306n))) : M.LE(1n+Nat.add(305n, B), _)
  %Equal.sym(Nat, Nat.add(B, 306n), Nat.add(306n, B), add_comm(B, 306n)) : M.LE(1n+Nat.add(305n, B), _)
  le_refl(Nat.add(306n, B))

# the law: done with budget + 306 fuel
def lane_ends(+heap: M.Heap, +cx: M.Cx, +budget: Nat, +root: M.T, +acc: M.Acc, +marks: List<&2, Nat>, +seen: List<&2, Nat>)
  -> {M.lane_done(heap, cx, budget, root, acc, marks, seen) == True{} : Bool}:
  ist_eq(M.lane_done(heap, cx, budget, root, acc, marks, seen),
    go_ends(heap, cx, budget, Nat.add(budget, 306n), M.S{M.Pop{}, M.R{[root], acc, marks, seen}, M.Idle{}}, M.ctr0(),
      Inl{((Unit{}, Unit{}), fuel0(budget))}))
