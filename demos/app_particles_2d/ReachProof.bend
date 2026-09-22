# ReachModel -- the proofs of ReachLaws.bend. The fuel laws do not open
# step: go counts, one fuel a step, and tally adds exactly one to one
# count, whatever the step did. The read laws follow rd's recursion.
# The bound is ReachBound.bend's, which opens every branch of step.
import Base
import ./ReachModel.bend as M
import ./ReachLaws.bend as Laws
import ./ReachBound.bend as Bd

# Nat and LE
# ----------

# a <= a + b
def le_plus(+a: Nat, +b: Nat) -> M.LE(a, Nat.add(a, b)):
  match a:
    case 0n:
      Unit{}
    case 1n+p:
      le_plus(p, b)

# Counts
# ------

# reads <= words <= steps, for any counts
def ctr_counts(+c: M.Ctr) -> (M.LE(M.Ctr.reads(c), M.Ctr.words(c)) & M.LE(M.Ctr.words(c), M.Ctr.steps(c))):
  match c:
    case M.Ctr{p, r, w, i}:
      (le_plus(r, w), Bd.le_prefix(p, Nat.add(r, w)))

# idle + steps
def spent(+c: M.Ctr) -> Nat:
  Nat.add(M.Ctr.idles(c), M.Ctr.steps(c))

# tally adds one, whatever the step did
def tally_one(+c: M.Ctr, +k: M.K) -> {spent(M.tally(c, k)) == 1n+spent(c) : Nat}:
  match c k:
    case M.Ctr{p, r, w, i} M.Idle{}:
      {==}
    case M.Ctr{p, r, w, i} M.Popd{}:
      Bd.add_succ(i, Nat.add(p, Nat.add(r, w)))
    case M.Ctr{p, r, w, i} M.Read{}:
      %Equal.sym(Nat, Nat.add(p, 1n+Nat.add(r, w)), 1n+Nat.add(p, Nat.add(r, w)), Bd.add_succ(p, Nat.add(r, w)))
        : {Nat.add(i, _) == 1n+Nat.add(i, Nat.add(p, Nat.add(r, w))) : Nat}
      Bd.add_succ(i, Nat.add(p, Nat.add(r, w)))
    case M.Ctr{p, r, w, i} M.Walk{}:
      %Equal.sym(Nat, Nat.add(r, 1n+w), 1n+Nat.add(r, w), Bd.add_succ(r, w))
        : {Nat.add(i, Nat.add(p, _)) == 1n+Nat.add(i, Nat.add(p, Nat.add(r, w))) : Nat}
      %Equal.sym(Nat, Nat.add(p, 1n+Nat.add(r, w)), 1n+Nat.add(p, Nat.add(r, w)), Bd.add_succ(p, Nat.add(r, w)))
        : {Nat.add(i, _) == 1n+Nat.add(i, Nat.add(p, Nat.add(r, w))) : Nat}
      Bd.add_succ(i, Nat.add(p, Nat.add(r, w)))

# go spends its fuel exactly: one count a fuel
def go_fuel(+heap: M.Heap, +cx: M.Cx, +budget: Nat, +fuel: Nat, +s: M.S<M.hl(heap)>, +c: M.Ctr)
  -> {spent(M.Lane.c(M.hl(heap), M.go(heap, cx, budget, fuel, s, c))) == Nat.add(fuel, spent(c)) : Nat}:
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      +s2 = M.step(heap, cx, budget, M.Ctr.steps(c), s)
      +c2 = M.tally(c, M.S.last(M.hl(heap), s2))
      %Bd.add_succ(f, spent(c))
        : {spent(M.Lane.c(M.hl(heap), M.go(heap, cx, budget, 1n+f, s, c))) == _ : Nat}
      %tally_one(c, M.S.last(M.hl(heap), s2))
        : {spent(M.Lane.c(M.hl(heap), M.go(heap, cx, budget, 1n+f, s, c))) == Nat.add(f, _) : Nat}
      go_fuel(heap, cx, budget, f, s2, c2)

# The laws
# --------

def Laws.lane_fuel(heap, cx, budget, fuel, root, acc, marks, seen):
  Equal.trans(Nat,
    spent(M.lane_ctr(heap, cx, budget, fuel, root, acc, marks, seen)),
    Nat.add(fuel, 0n),
    fuel,
    go_fuel(heap, cx, budget, fuel, M.S{M.Pop{}, M.R{[root], acc, marks, seen}, M.Idle{}}, M.ctr0()),
    Bd.add_zero(fuel))

def Laws.lane_counts(heap, cx, budget, fuel, root, acc, marks, seen):
  ctr_counts(M.lane_ctr(heap, cx, budget, fuel, root, acc, marks, seen))

def Laws.lane_reads(heap, cx, budget, fuel, root, acc, marks, seen):
  +c = M.lane_ctr(heap, cx, budget, fuel, root, acc, marks, seen)
  %Laws.lane_fuel(heap, cx, budget, fuel, root, acc, marks, seen) : M.LE(M.Ctr.reads(c), _)
  Bd.le_trans(M.Ctr.reads(c), M.Ctr.words(c), spent(c),
    Pair.fst(M.LE(M.Ctr.reads(c), M.Ctr.words(c)), M.LE(M.Ctr.words(c), M.Ctr.steps(c)), ctr_counts(c)),
    Bd.le_trans(M.Ctr.words(c), M.Ctr.steps(c), spent(c),
      Pair.snd(M.LE(M.Ctr.reads(c), M.Ctr.words(c)), M.LE(M.Ctr.words(c), M.Ctr.steps(c)), ctr_counts(c)),
      Bd.le_prefix(M.Ctr.idles(c), M.Ctr.steps(c))))

# rd is List.get where it may read
def rd_get(-A: Data, +xs: List<&2, A>, +i: Nat, +e: M.LE(1n+i, List.length(&2, A, xs)))
  -> {List.get(&2, A, xs, i) == Some{M.rd(A, xs, i, e)} : Maybe<&2, A>}:
  match xs i:
    case Nil{} _:
      match e:
    case h <> t 0n:
      {==}
    case h <> t 1n+j:
      rd_get(A, t, j, e)

def Laws.heap_read(ws, i, e):
  rd_get(M.W, ws, i, e)

def Laws.table_read(xs, i, e):
  rd_get(Nat, xs, i, e)

def Laws.lane_ends(heap, cx, budget, root, acc, marks, seen):
  Bd.lane_ends(heap, cx, budget, root, acc, marks, seen)
