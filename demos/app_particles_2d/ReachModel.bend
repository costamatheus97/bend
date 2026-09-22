# ReachModel -- a model of reach.c's walker: reach_dev's lane and
# at_walk1's rounds, over a heap given as a list of 64-bit words (each
# as its bits above and below bit 24, since a Nat is at most 2^48).
# ReachLaws.bend states what it guarantees, ReachProof.bend proves it
# (the lane bound by ReachBound.bend). The same structure
# as the C, in its order: a pop checks the word for a leaf, then (strict)
# for an argument word, then the lane's budget; a node's tag and table
# index are checked before its size is read, and its size against lim
# before its words; a block over 2^RC_PIECE words goes back as halves; a
# full stack sends a word to the next round; the rounds stop at their cap,
# or once the walk's steps pass rall, checked before each dispatch.
#
# Defs come before their callers (Bend's rule), so each chain reads
# upward. A lane is a machine that makes one C step a fuel: a pop, or
# one word of a node (read, or only counted, as a BUF's). Every heap and
# table read goes through rd, which takes live evidence that its index
# is in range, built from the check the C makes: there is no other read.
import Base


# Order and evidence
# ------------------

# LE(a, b): a proof of a <= b (Unit), or of nothing (Empty)
def LE(a: Nat, b: Nat) -> Data:
  match a b:
    case 0n _:
      Unit
    case 1n+p 0n:
      Empty
    case 1n+p 1n+q:
      LE(p, q)

# a < b, or b <= a, with its evidence
def lt_dec(a: Nat, b: Nat) -> Or(LE(1n+a, b), LE(b, a)):
  match a b:
    case 0n 0n:
      Inr{Unit{}}
    case 0n 1n+q:
      Inl{Unit{}}
    case 1n+p 0n:
      Inr{Unit{}}
    case 1n+p 1n+q:
      lt_dec(p, q)

def le_pred(+a: Nat, +b: Nat, e: LE(1n+a, b)) -> LE(a, b):
  match a b:
    case 0n _:
      Unit{}
    case 1n+p 0n:
      Empty.absurd(LE(1n+p, 0n), e)
    case 1n+p 1n+q:
      le_pred(p, q, e)

# the one read: xs[i], given i < length(xs); the Nil case is refuted
def rd(-A: Data, xs: List<&2, A>, i: Nat, e: LE(1n+i, List.length(&2, A, xs))) -> A:
  match xs i:
    case Nil{} _:
      match e:
    case h <> t 0n:
      h
    case h <> t 1n+j:
      rd(A, t, j, e)

# Words and terms
# ---------------

# a heap word: bits 24..63 and 0..23
type W is Data:
  W{hi: Nat, lo: Nat}

# a term: RFC_BIT, tag (bits 56..62), aux (40..55), loc (0..39)
type T is Data:
  T{rfc: Bool, tag: Nat, aux: Nat, loc: Nat}

def pow2(n: Nat) -> Nat:
  Nat.pow(2n, n)

# by comparison, not by recursion on the Nats (Base's recurse)
def min(+a: Nat, +b: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_lt(a, b), a, b)

def max(+a: Nat, +b: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_lt(a, b), b, a)

def decode(w: W) -> T:
  match w:
    case W{+hi, lo}:
      T{Nat.is_eq(Nat.div(hi, pow2(39n)), 1n), Nat.mod(Nat.div(hi, pow2(32n)), 128n),
        Nat.mod(Nat.div(hi, 65536n), 65536n), Nat.add(Nat.mul(Nat.mod(hi, 65536n), pow2(24n)), lo)}

# H[l] >> 24: where a sealed cell points
def cell(w: W) -> Nat:
  match w:
    case W{hi, lo}:
      hi

def is_hole(rfc: Bool, tag: Nat, aux: Nat, loc: Nat) -> Bool:
  Bool.and(rfc, Bool.and(Nat.is_eq(tag, 127n), Bool.and(Nat.is_eq(aux, 65535n),
    Nat.is_eq(loc, Nat.sub(pow2(40n), 1n)))))

# term_triv: a leaf, TERM_HOLE, or below the heap
def triv(+off: Nat, t: T) -> Bool:
  match t:
    case T{rfc, +tag, +aux, +loc}:
      Bool.or(Nat.is_le(tag, 1n), Bool.or(is_hole(rfc, tag, aux, loc), Nat.is_lt(loc, off)))

def teq(a: T, b: T) -> Bool:
  match a b:
    case T{ar, at, aa, al} T{br, bt, ba, bl}:
      Bool.and(Cmp.is_eq(Bool.cmp(ar, br)), Bool.and(Nat.is_eq(at, bt),
        Bool.and(Nat.is_eq(aa, ba), Nat.is_eq(al, bl))))

def tmem(+t: T, xs: List<&2, T>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> r:
      Bool.or(teq(t, h), tmem(t, r))

def nmem(+n: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> r:
      Bool.or(Nat.is_eq(n, h), nmem(n, r))

def nadd(+n: Nat, +xs: List<&2, Nat>) -> List<&2, Nat>:
  Bool.pick(List<&2, Nat>, nmem(n, xs), xs, n <> xs)

# The walk's inputs
# -----------------

# off: HEAP_OFF (the heap list is [off, off + its length)); ctab, ftab:
# CID_ARITY_T, FID_ARITY_T; lo, hi: the tracked words (marks); args: the
# bang's argument words (strict walks stop there); qcap: the queue's cap;
# rcap: the rounds' (4096); rall: RC_ALL
type Cx is Data:
  Cx{off: Nat, ctab: List<&2, Nat>, ftab: List<&2, Nat>, lo: Nat, hi: Nat, follow: Bool,
    args: List<&2, T>, qcap: Nat, rcap: Nat, rall: Nat}

def Cx.off(cx: Cx) -> Nat:
  match cx:
    case Cx{off, ctab, ftab, lo, hi, follow, args, qcap, rcap, rall}:
      off

def Cx.ctab(cx: Cx) -> List<&2, Nat>:
  match cx:
    case Cx{off, ctab, ftab, lo, hi, follow, args, qcap, rcap, rall}:
      ctab

def Cx.ftab(cx: Cx) -> List<&2, Nat>:
  match cx:
    case Cx{off, ctab, ftab, lo, hi, follow, args, qcap, rcap, rall}:
      ftab

def Cx.lo(cx: Cx) -> Nat:
  match cx:
    case Cx{off, ctab, ftab, lo, hi, follow, args, qcap, rcap, rall}:
      lo

def Cx.hi(cx: Cx) -> Nat:
  match cx:
    case Cx{off, ctab, ftab, lo, hi, follow, args, qcap, rcap, rall}:
      hi

def Cx.follow(cx: Cx) -> Bool:
  match cx:
    case Cx{off, ctab, ftab, lo, hi, follow, args, qcap, rcap, rall}:
      follow

def Cx.args(cx: Cx) -> List<&2, T>:
  match cx:
    case Cx{off, ctab, ftab, lo, hi, follow, args, qcap, rcap, rall}:
      args

def Cx.qcap(cx: Cx) -> Nat:
  match cx:
    case Cx{off, ctab, ftab, lo, hi, follow, args, qcap, rcap, rall}:
      qcap

def Cx.rcap(cx: Cx) -> Nat:
  match cx:
    case Cx{off, ctab, ftab, lo, hi, follow, args, qcap, rcap, rall}:
      rcap

def Cx.rall(cx: Cx) -> Nat:
  match cx:
    case Cx{off, ctab, ftab, lo, hi, follow, args, qcap, rcap, rall}:
      rall

# RC_STACK, 2^RC_PIECE, RC_SLACK, RC_LANES, RC_WORK, 2^18 bytes in words
def rc_stack() -> Nat:
  48n

def rc_piece() -> Nat:
  256n

def rc_slack() -> Nat:
  306n

def rc_lanes() -> Nat:
  pow2(15n)

def rc_work() -> Nat:
  pow2(24n)

def chunk_words() -> Nat:
  pow2(15n)

# the heap: its words and their count, with the proof that it is theirs
type Heap is Data:
  Heap{ws: List<&2, W>, len: Nat, q: {len == List.length(&2, W, ws) : Nat}}

def hl(heap: Heap) -> Nat:
  match heap:
    case Heap{ws, len, q}:
      len

# H[i], given i < len
def Heap.read(heap: Heap, i: Nat, e: LE(1n+i, hl(heap))) -> W:
  match heap:
    case Heap{ws, len, q}:
      rd(W, ws, i, (%q : LE(1n+i, _); e))

def reach_budget.fin(few: Bool, +b: Nat) -> Nat:
  match few:
    case True{}:
      64n
    case False{}:
      min(max(b, 64n), 16384n)

# reach_budget
def reach_budget(+nin: Nat) -> Nat:
  reach_budget.fin(Nat.is_lt(nin, 4096n), Nat.div(rc_work(), min(nin, rc_lanes())))

# reach_span
# ----------

type Sp is Data:
  Bad{}
  Sp{n: Nat, kids: Bool}

def tab.fin(+xs: List<&2, Nat>, +i: Nat, c: Or(LE(1n+i, List.length(&2, Nat, xs)), LE(List.length(&2, Nat, xs), i))) -> Maybe<&2, Nat>:
  match c:
    case Inl{e}:
      Some{rd(Nat, xs, i, e)}
    case Inr{e}:
      None{}

# T[i], or None past the table: the C checks i before it reads
def tab(+xs: List<&2, Nat>, +i: Nat) -> Maybe<&2, Nat>:
  tab.fin(xs, i, lt_dec(i, List.length(&2, Nat, xs)))

def span.ctr(m: Maybe<&2, Nat>) -> Sp:
  match m:
    case None{}:
      Bad{}
    case Some{a}:
      Sp{a, True{}}

# a closure of arity 0 is bad; else its captures
def span.clo(m: Maybe<&2, Nat>) -> Sp:
  match m:
    case None{}:
      Bad{}
    case Some{a}:
      match a:
        case 0n:
          Bad{}
        case 1n+p:
          Sp{p, True{}}

def span.tsk(m: Maybe<&2, Nat>) -> Sp:
  match m:
    case None{}:
      Bad{}
    case Some{a}:
      Sp{Nat.add(a, 2n), False{}}

# buf_wcls
def buf_w(c: Nat) -> Nat:
  match c:
    case 0n:
      0n
    case 1n+p:
      p

# by tag: CTR 2, CLO 3, BUF 4, TSK 5, ARR 6; any other is bad
def span.tag(+ctab: List<&2, Nat>, +ftab: List<&2, Nat>, tag: Nat, +aux: Nat) -> Sp:
  match tag:
    case 0n:
      Bad{}
    case 1n+t1:
      match t1:
        case 0n:
          Bad{}
        case 1n+t2:
          match t2:
            case 0n:
              span.ctr(tab(ctab, aux))
            case 1n+t3:
              match t3:
                case 0n:
                  span.clo(tab(ftab, aux))
                case 1n+t4:
                  match t4:
                    case 0n:
                      Sp{pow2(buf_w(Nat.mod(aux, 32n))), False{}}
                    case 1n+t5:
                      match t5:
                        case 0n:
                          span.tsk(tab(ftab, aux))
                        case 1n+t6:
                          match t6:
                            case 0n:
                              Sp{pow2(Nat.mod(aux, 32n)), True{}}
                            case 1n+t7:
                              Bad{}

def span(+ctab: List<&2, Nat>, +ftab: List<&2, Nat>, t: T) -> Sp:
  match t:
    case T{rfc, tag, aux, loc}:
      span.tag(ctab, ftab, tag, aux)

# The lane
# --------

# what a lane holds besides its stack: the words sent to the next round
# (last first) and their count, bad nodes (and the first), blocks split,
# argument words met
type Acc is Data:
  Acc{out: List<&2, T>, nout: Nat, bad: Nat, fbad: Maybe<&2, T>, split: Nat, hits: Nat}

# the stack (top first), the lane's Acc, the chunks marked, the sealed
# cells gone through (relative to off)
type R is Data:
  R{st: List<&2, T>, acc: Acc, marks: List<&2, Nat>, seen: List<&2, Nat>}

# Pop: pop the next word. Kids: a node's words [i, i + j) are left to
# read, last first, each pushed. Leaf: j words left to count. Cell: a
# sealed cell at i, to go through. Each carries its evidence.
type Mode<-len: Nat> is Data:
  Pop{}
  Kids{i: Nat, j: Nat, e: LE(Nat.add(j, i), len)}
  Leaf{j: Nat}
  Cell{t: T, i: Nat, e: LE(1n+i, len)}

# what the last step did: nothing (done), a pop, a read, a word counted
type K is Data:
  Idle{}
  Popd{}
  Read{}
  Walk{}

type S<-len: Nat> is Data:
  S{mode: Mode<len>, r: R, last: K}

def r_spill(t: T, r: R) -> R:
  match r:
    case R{st, acc, marks, seen}:
      match acc:
        case Acc{out, nout, bad, fbad, split, hits}:
          R{st, Acc{t <> out, 1n+nout, bad, fbad, split, hits}, marks, seen}

def first(m: Maybe<&2, T>, t: T) -> Maybe<&2, T>:
  match m:
    case None{}:
      Some{t}
    case Some{x}:
      Some{x}

def r_bad(t: T, r: R) -> R:
  match r:
    case R{st, acc, marks, seen}:
      match acc:
        case Acc{out, nout, bad, fbad, split, hits}:
          R{st, Acc{out, nout, 1n+bad, first(fbad, t), split, hits}, marks, seen}

def r_split(r: R) -> R:
  match r:
    case R{st, acc, marks, seen}:
      match acc:
        case Acc{out, nout, bad, fbad, split, hits}:
          R{st, Acc{out, nout, bad, fbad, 1n+split, hits}, marks, seen}

def r_hit(r: R) -> R:
  match r:
    case R{st, acc, marks, seen}:
      match acc:
        case Acc{out, nout, bad, fbad, split, hits}:
          R{st, Acc{out, nout, bad, fbad, split, 1n+hits}, marks, seen}

def r_has(+i: Nat, r: R) -> Bool:
  match r:
    case R{st, acc, marks, seen}:
      nmem(i, seen)

def r_see(+i: Nat, r: R) -> R:
  match r:
    case R{st, acc, marks, seen}:
      R{st, acc, marks, nadd(i, seen)}

def r_push.fin(room: Bool, t: T, st: List<&2, T>, acc: Acc, marks: List<&2, Nat>, seen: List<&2, Nat>) -> R:
  match room:
    case True{}:
      R{t <> st, acc, marks, seen}
    case False{}:
      r_spill(t, R{st, acc, marks, seen})

# push t, or send it to the next round when the stack is full
def r_push(t: T, r: R) -> R:
  match r:
    case R{+st, acc, marks, seen}:
      r_push.fin(Nat.is_lt(List.length(&2, T, st), rc_stack()), t, st, acc, marks, seen)

def r_kid.fin(leaf: Bool, t: T, r: R) -> R:
  match leaf:
    case True{}:
      r
    case False{}:
      r_push(t, r)

# a node's word: pushed unless it is a leaf
def r_kid(+off: Nat, +t: T, r: R) -> R:
  r_kid.fin(triv(off, t), t, r)

def r_mark.fin(+cx: Cx, +l: Nat, +m: Nat, ok: Bool, r: R) -> R:
  match ok:
    case False{}:
      r
    case True{}:
      match r:
        case R{st, acc, marks, seen}:
          R{st, acc, nadd(Nat.div(Nat.sub(Nat.sub(Nat.add(l, m), Cx.lo(cx)), 1n), chunk_words()),
            nadd(Nat.div(Nat.sub(l, Cx.lo(cx)), chunk_words()), marks)), seen}

# the chunks of words [l, l + m) when all of them are tracked
def r_mark(+cx: Cx, +l: Nat, +m: Nat, r: R) -> R:
  r_mark.fin(cx, l, m, Bool.and(Nat.is_le(Cx.lo(cx), l), Nat.is_le(Nat.add(l, m), Cx.hi(cx))), r)

# The z loop's body, for a word past the pop's checks (or a sealed
# cell's target), entry below: a sealed cell is one word; else the tag
# and table index give the size, then lim, then the split. Each def
# comes before its callers, so the chain reads upward.
def tloc(t: T) -> Nat:
  match t:
    case T{rfc, tag, aux, loc}:
      loc

def rel(+cx: Cx, +t: T) -> Nat:
  Nat.sub(tloc(t), Cx.off(cx))

def half.fin(c: Nat, rfc: Bool, tag: Nat, +aux: Nat, +l: Nat) -> T:
  match c:
    case 0n:
      T{True{}, 127n, 65535n, l}
    case 1n+p:
      T{rfc, tag, Nat.sub(aux, 1n), l}

# a block's half: class one less (a class 0 wraps as the C's does)
def half(t: T, +l: Nat) -> T:
  match t:
    case T{rfc, tag, +aux, loc}:
      half.fin(Nat.mod(aux, 32n), rfc, tag, aux, l)

def entry.words(+heap: Heap, +cx: Cx, +t: T, +k: Nat, kids: Bool,
  e: LE(1n+Nat.add(k, rel(cx, t)), hl(heap)), r: R, last: K) -> S<hl(heap)>:
  match kids:
    case True{}:
      S{Kids{rel(cx, t), 1n+k, e}, r, last}
    case False{}:
      S{Leaf{1n+k}, r, last}

def entry.fit(+heap: Heap, +cx: Cx, +t: T, +k: Nat, kids: Bool,
  e: LE(1n+Nat.add(k, rel(cx, t)), hl(heap)), big: Bool, r: R, last: K) -> S<hl(heap)>:
  match big:
    case True{}:
      S{Pop{}, r_split(r_push(half(t, tloc(t)), r_push(half(t, Nat.add(tloc(t), Nat.div(1n+k, 2n))), r))), last}
    case False{}:
      entry.words(heap, cx, t, k, kids, e, r_mark(cx, tloc(t), 1n+k, r), last)

# n = 1 + k words at rel .. rel + n, in range when c says so
def entry.some(+heap: Heap, +cx: Cx, +t: T, +k: Nat, kids: Bool,
  c: Or(LE(1n+Nat.add(k, rel(cx, t)), hl(heap)), LE(hl(heap), Nat.add(k, rel(cx, t)))), r: R, last: K) -> S<hl(heap)>:
  match c:
    case Inl{e}:
      entry.fit(heap, cx, t, k, kids, e, Nat.is_lt(rc_piece(), 1n+k), r, last)
    case Inr{e}:
      S{Pop{}, r_bad(t, r), last}

def entry.none(+heap: Heap, +cx: Cx, +t: T, c: Or(LE(1n+rel(cx, t), hl(heap)), LE(hl(heap), rel(cx, t))), r: R, last: K) -> S<hl(heap)>:
  match c:
    case Inl{e}:
      S{Pop{}, r_mark(cx, tloc(t), 1n, r), last}
    case Inr{e}:
      S{Pop{}, r_bad(t, r), last}

# no words: lim still checked on one, as n ? n : 1
def entry.n(+heap: Heap, +cx: Cx, +t: T, n: Nat, kids: Bool, r: R, last: K) -> S<hl(heap)>:
  match n:
    case 0n:
      entry.none(heap, cx, t, lt_dec(rel(cx, t), hl(heap)), r, last)
    case 1n++k:
      entry.some(heap, cx, t, k, kids, lt_dec(Nat.add(k, rel(cx, t)), hl(heap)), r, last)

def entry.span(+heap: Heap, +cx: Cx, +t: T, sp: Sp, r: R, last: K) -> S<hl(heap)>:
  match sp:
    case Bad{}:
      S{Pop{}, r_bad(t, r), last}
    case Sp{n, kids}:
      entry.n(heap, cx, t, n, kids, r, last)

def entry.cell(+heap: Heap, +cx: Cx, +t: T, +i: Nat, c: Or(LE(1n+i, hl(heap)), LE(hl(heap), i)), r: R, last: K) -> S<hl(heap)>:
  match c:
    case Inl{e}:
      S{Cell{t, i, e}, r_mark(cx, tloc(t), 1n, r), last}
    case Inr{e}:
      S{Pop{}, r_bad(t, r), last}

def entry.go(+heap: Heap, +cx: Cx, rfc: Bool, +t: T, r: R, last: K) -> S<hl(heap)>:
  match rfc:
    case True{}:
      entry.cell(heap, cx, t, rel(cx, t), lt_dec(rel(cx, t), hl(heap)), r, last)
    case False{}:
      entry.span(heap, cx, t, span(Cx.ctab(cx), Cx.ftab(cx), t), r, last)

def entry(+heap: Heap, +cx: Cx, +t: T, r: R, last: K) -> S<hl(heap)>:
  match t:
    case T{rfc, tag, aux, loc}:
      entry.go(heap, cx, rfc, t, r, last)

# The steps
# ---------

# a node's next word, from the last: read and pushed unless a leaf
def kids.step(+heap: Heap, +cx: Cx, +i: Nat, +j: Nat, +e: LE(1n+Nat.add(j, i), hl(heap)), r: R) -> S<hl(heap)> :
  S{Kids{i, j, le_pred(Nat.add(j, i), hl(heap), e)}, r_kid(Cx.off(cx), decode(Heap.read(heap, Nat.add(j, i), e)), r), Read{}}

def cell.to.fin(+heap: Heap, +cx: Cx, leaf: Bool, +t: T, r: R) -> S<hl(heap)>:
  match leaf:
    case True{}:
      S{Pop{}, r, Read{}}
    case False{}:
      entry(heap, cx, t, r, Read{})

def cell.to(+heap: Heap, +cx: Cx, +t: T, r: R) -> S<hl(heap)>:
  cell.to.fin(heap, cx, triv(Cx.off(cx), t), t, r)

def cell.fin(+heap: Heap, +cx: Cx, go: Bool, t: T, +i: Nat, e: LE(1n+i, hl(heap)), r: R) -> S<hl(heap)>:
  match go:
    case False{}:
      S{Pop{}, r, Walk{}}
    case True{}:
      match t:
        case T{rfc, tag, aux, loc}:
          cell.to(heap, cx, T{False{}, tag, aux, cell(Heap.read(heap, i, e))}, r_see(i, r))

# a sealed cell: strict stops; full goes through once, to what it holds,
# as a term of the cell's tag and aux (the RFC bit cleared)
def cell.step(+heap: Heap, +cx: Cx, t: T, +i: Nat, e: LE(1n+i, hl(heap)), +r: R) -> S<hl(heap)>:
  cell.fin(heap, cx, Bool.and(Cx.follow(cx), Bool.not(r_has(i, r))), t, i, e, r)

def pop.over(+heap: Heap, +cx: Cx, over: Bool, +t: T, r: R) -> S<hl(heap)>:
  match over:
    case True{}:
      S{Pop{}, r_spill(t, r), Popd{}}
    case False{}:
      entry(heap, cx, t, r, Popd{})

def pop.arg(+heap: Heap, +cx: Cx, +budget: Nat, +steps: Nat, arg: Bool, +t: T, r: R) -> S<hl(heap)>:
  match arg:
    case True{}:
      S{Pop{}, r_hit(r), Popd{}}
    case False{}:
      pop.over(heap, cx, Nat.is_le(budget, steps), t, r)

def pop.leaf(+heap: Heap, +cx: Cx, +budget: Nat, +steps: Nat, leaf: Bool, +t: T, r: R) -> S<hl(heap)>:
  match leaf:
    case True{}:
      S{Pop{}, r, Popd{}}
    case False{}:
      pop.arg(heap, cx, budget, steps, Bool.and(Bool.not(Cx.follow(cx)), tmem(t, Cx.args(cx))), t, r)

# a pop: a leaf goes; (strict) an argument word counts and goes; past
# the budget (steps counts this pop) the word goes to the next round
def pop.step(+heap: Heap, +cx: Cx, +budget: Nat, +steps: Nat, r: R) -> S<hl(heap)>:
  match r:
    case R{st, acc, marks, seen}:
      match st:
        case Nil{}:
          S{Pop{}, R{Nil{}, acc, marks, seen}, Idle{}}
        case +h <> rest:
          pop.leaf(heap, cx, budget, steps, triv(Cx.off(cx), h), h, R{rest, acc, marks, seen})

# one C step; steps: the lane's so far
def step(+heap: Heap, +cx: Cx, +budget: Nat, +steps: Nat, s: S<hl(heap)>) -> S<hl(heap)>:
  match s:
    case S{mode, r, last}:
      match mode:
        case Pop{}:
          pop.step(heap, cx, budget, steps, r)
        case Kids{i, 0n, e}:
          pop.step(heap, cx, budget, steps, r)
        case Kids{i, 1n+j, e}:
          kids.step(heap, cx, i, j, e, r)
        case Leaf{0n}:
          pop.step(heap, cx, budget, steps, r)
        case Leaf{1n+j}:
          S{Leaf{j}, r, Walk{}}
        case Cell{t, i, e}:
          cell.step(heap, cx, t, i, e, r)

# the lane's counts: pops, words read, words counted, idle fuel
type Ctr is Data:
  Ctr{pops: Nat, reads: Nat, walks: Nat, idles: Nat}

def Ctr.steps(c: Ctr) -> Nat:
  match c:
    case Ctr{p, r, w, i}:
      Nat.add(p, Nat.add(r, w))

def Ctr.reads(c: Ctr) -> Nat:
  match c:
    case Ctr{p, r, w, i}:
      r

def Ctr.words(c: Ctr) -> Nat:
  match c:
    case Ctr{p, r, w, i}:
      Nat.add(r, w)

def Ctr.idles(c: Ctr) -> Nat:
  match c:
    case Ctr{p, r, w, i}:
      i

def S.last(-len: Nat, s: S<len>) -> K:
  match s:
    case S{mode, r, last}:
      last

def tally(c: Ctr, k: K) -> Ctr:
  match c:
    case Ctr{p, r, w, i}:
      match k:
        case Idle{}:
          Ctr{p, r, w, 1n+i}
        case Popd{}:
          Ctr{1n+p, r, w, i}
        case Read{}:
          Ctr{p, 1n+r, w, i}
        case Walk{}:
          Ctr{p, r, 1n+w, i}

type Lane<-len: Nat> is Data:
  Lane{s: S<len>, c: Ctr}

def Lane.c(-len: Nat, l: Lane<len>) -> Ctr:
  match l:
    case Lane{s, c}:
      c

# one step a fuel; the counting is here, not in step
def go(+heap: Heap, +cx: Cx, +budget: Nat, fuel: Nat, s: S<hl(heap)>, +c: Ctr) -> Lane<hl(heap)>:
  match fuel:
    case 0n:
      Lane{s, c}
    case 1n+f:
      +s2 = step(heap, cx, budget, Ctr.steps(c), s)
      go(heap, cx, budget, f, s2, tally(c, S.last(hl(heap), s2)))

def ctr0() -> Ctr:
  Ctr{0n, 0n, 0n, 0n}

# a lane: its word on the stack, fuel budget + RC_SLACK
def lane(+heap: Heap, +cx: Cx, +budget: Nat, fuel: Nat, root: T, acc: Acc, marks: List<&2, Nat>, seen: List<&2, Nat>) -> Lane<hl(heap)>:
  go(heap, cx, budget, fuel, S{Pop{}, R{[root], acc, marks, seen}, Idle{}}, ctr0())

def Mode.idle(-len: Nat, m: Mode<len>) -> Bool:
  match m:
    case Pop{}:
      True{}
    case Kids{i, j, e}:
      Nat.is_eq(j, 0n)
    case Leaf{j}:
      Nat.is_eq(j, 0n)
    case Cell{t, i, e}:
      False{}

# done: nothing on the stack, no node under way
def S.done(-len: Nat, s: S<len>) -> Bool:
  match s:
    case S{mode, r, last}:
      match r:
        case R{st, acc, marks, seen}:
          match st:
            case Nil{}:
              Mode.idle(len, mode)
            case h <> t:
              False{}

# The rounds
# ----------

# a walk's totals: rounds, steps, words, reads, most steps a lane,
# lanes out of fuel, rounds whose queue overflowed, why it stopped (0
# drained, 1 round cap, 2 step cap)
type Tot is Data:
  Tot{rounds: Nat, steps: Nat, words: Nat, reads: Nat, lanemax: Nat, starved: Nat, over: Nat, why: Nat}

# a round under way: the next dispatch may start (ok), its steps so far
type Rd is Data:
  Rd{ok: Bool, rs: Nat, acc: Acc, marks: List<&2, Nat>, seen: List<&2, Nat>, tot: Tot}

def bump(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}:
      1n+n
    case False{}:
      n

def after(+cx: Cx, +all: Nat, rs: Nat, -len: Nat, l: Lane<len>, tot: Tot) -> Rd:
  match l:
    case Lane{+s, +c}:
      match s:
        case S{mode, r, last}:
          match r:
            case R{st, acc, marks, seen}:
              match tot:
                case Tot{rounds, steps, words, reads, lanemax, starved, over, why}:
                  +rs2 = Nat.add(rs, Ctr.steps(c))
                  Rd{Nat.is_le(Nat.add(all, rs2), Cx.rall(cx)), rs2, acc, marks, seen,
                    Tot{rounds, Nat.add(steps, Ctr.steps(c)), Nat.add(words, Ctr.words(c)),
                      Nat.add(reads, Ctr.reads(c)), max(lanemax, Ctr.steps(c)),
                      bump(Bool.not(S.done(len, s)), starved), over, why}}

# a round's lanes in order, RC_LANES a dispatch; a dispatch starts only
# while all + the round's steps <= rall (k: lanes left in this one)
def lanes(+heap: Heap, +cx: Cx, +budget: Nat, +all: Nat, q: List<&2, T>, k: Nat, rd: Rd) -> Rd:
  match q:
    case Nil{}:
      rd
    case t <> rest:
      match k:
        case 0n:
          match rd:
            case Rd{ok, rs, acc, marks, seen, tot}:
              match ok:
                case False{}:
                  Rd{False{}, rs, acc, marks, seen, tot}
                case True{}:
                  lanes(heap, cx, budget, all, rest, Nat.sub(rc_lanes(), 1n),
                    after(cx, all, rs, hl(heap), lane(heap, cx, budget, Nat.add(budget, rc_slack()), t, acc, marks, seen), tot))
        case 1n+k2:
          match rd:
            case Rd{ok, rs, acc, marks, seen, tot}:
              lanes(heap, cx, budget, all, rest, k2,
                after(cx, all, rs, hl(heap), lane(heap, cx, budget, Nat.add(budget, rc_slack()), t, acc, marks, seen), tot))

# between rounds: the next queue, its first qcap words in order
type Pre is Data:
  Pre{q: List<&2, T>, nq: Nat, all: Nat, stop: Bool, acc: Acc, marks: List<&2, Nat>, seen: List<&2, Nat>, tot: Tot}

def post(+cx: Cx, +all: Nat, rd: Rd) -> Pre:
  match rd:
    case Rd{ok, rs, acc, marks, seen, tot}:
      match acc:
        case Acc{out, +nout, bad, fbad, split, hits}:
          match tot:
            case Tot{rounds, steps, words, reads, lanemax, starved, over, why}:
              +all2 = Nat.add(all, rs)
              Pre{List.reverse(&2, T, List.drop(&2, T, out, Nat.sub(nout, Cx.qcap(cx)))), min(nout, Cx.qcap(cx)), all2,
                Nat.is_lt(Cx.rall(cx), all2), Acc{Nil{}, 0n, bad, fbad, split, hits}, marks, seen,
                Tot{1n+rounds, steps, words, reads, lanemax, starved, bump(Nat.is_lt(Cx.qcap(cx), nout), over), why}}

# the result: totals, bad nodes and the first, splits, argument words
# met, chunks marked
type Out is Data:
  Out{tot: Tot, bad: Nat, fbad: Maybe<&2, T>, split: Nat, hits: Nat, marks: List<&2, Nat>}

def finish(why: Nat, acc: Acc, marks: List<&2, Nat>, tot: Tot) -> Out:
  match acc tot:
    case Acc{out, nout, bad, fbad, split, hits} Tot{rounds, steps, words, reads, lanemax, starved, over, w}:
      Out{Tot{rounds, steps, words, reads, lanemax, starved, over, why}, bad, fbad, split, hits, marks}

def rounds.cap(q: List<&2, T>) -> Nat:
  match q:
    case Nil{}:
      0n
    case h <> t:
      1n

# at_walk1's loop: while words are queued, a round unless past rcap
# rounds or rall steps
def rounds(+heap: Heap, +cx: Cx, rf: Nat, p: Pre) -> Out:
  match rf p:
    case 0n Pre{q, nq, all, sp, acc, marks, seen, tot}:
      finish(rounds.cap(q), acc, marks, tot)
    case 1n+rf2 Pre{q, +nq, +all, sp, acc, marks, seen, tot}:
      match q sp:
        case Nil{} _:
          finish(0n, acc, marks, tot)
        case (t <> rest) True{}:
          finish(2n, acc, marks, tot)
        case (t <> rest) False{}:
          rounds(heap, cx, rf2, post(cx, all, lanes(heap, cx, reach_budget(nq), all, t <> rest, 0n,
            Rd{Nat.is_le(all, Cx.rall(cx)), 0n, acc, marks, seen, tot})))

def walk(+heap: Heap, +cx: Cx, +roots: List<&2, T>) -> Out:
  +n = List.length(&2, T, roots)
  rounds(heap, cx, Cx.rcap(cx), Pre{roots, n, 0n, False{}, Acc{Nil{}, 0n, 0n, None{}, 0n, 0n}, Nil{}, Nil{},
    Tot{0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}})

def Lane.s(-len: Nat, l: Lane<len>) -> S<len>:
  match l:
    case Lane{s, c}:
      s

# a lane's counts, and whether it ended (budget + RC_SLACK fuel), for the
# laws
def lane_ctr(+heap: Heap, +cx: Cx, +budget: Nat, fuel: Nat, root: T, acc: Acc, marks: List<&2, Nat>, seen: List<&2, Nat>) -> Ctr:
  Lane.c(hl(heap), lane(heap, cx, budget, fuel, root, acc, marks, seen))

def lane_done(+heap: Heap, +cx: Cx, +budget: Nat, root: T, acc: Acc, marks: List<&2, Nat>, seen: List<&2, Nat>) -> Bool:
  S.done(hl(heap), Lane.s(hl(heap), lane(heap, cx, budget, Nat.add(budget, rc_slack()), root, acc, marks, seen)))
