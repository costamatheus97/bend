# ReachModel -- the laws. A lane gets fuel and makes one C step a fuel:
# (a) it reads at most its fuel, (c) its counts agree: every fuel is a
# step or idle, a read is a word, a word is a step. (b) every read is in
# range: rd, the model's only read, takes live evidence i < length(xs)
# (so no out-of-range read type-checks) and is List.get's element there.
# (a) and (c) hold by construction (one step a fuel, whatever step
# does); that a Read tally is one Heap.read is by inspection of step.
# lane_ends is the bound with content: with budget + RC_SLACK fuel a lane
# ends, through every branch of step. ReachProof.bend proves them all,
# the bound by ReachBound.bend.
#
# What this covers: the proofs are about the model. A differential test
# (outside the repo: the commit-1 CPU harness's round loop over the
# spliced reach_dev, and this model through bend's JS interop) runs both
# on the same heaps and compares their counts; it links the model to
# the C on those inputs only. Nothing here proves the C.
import Base
import ./ReachModel.bend as M

# (a) reads <= fuel
law lane_reads:
  for +heap: M.Heap
  for +cx: M.Cx
  for +budget: Nat
  for +fuel: Nat
  for +root: M.T
  for +acc: M.Acc
  for +marks: List<&2, Nat>
  for +seen: List<&2, Nat>
  M.LE(M.Ctr.reads(M.lane_ctr(heap, cx, budget, fuel, root, acc, marks, seen)), fuel)

# (c) idle fuel + steps == fuel
law lane_fuel:
  for +heap: M.Heap
  for +cx: M.Cx
  for +budget: Nat
  for +fuel: Nat
  for +root: M.T
  for +acc: M.Acc
  for +marks: List<&2, Nat>
  for +seen: List<&2, Nat>
  {Nat.add(M.Ctr.idles(M.lane_ctr(heap, cx, budget, fuel, root, acc, marks, seen)),
    M.Ctr.steps(M.lane_ctr(heap, cx, budget, fuel, root, acc, marks, seen))) == fuel : Nat}

# (c) reads <= words <= steps
law lane_counts:
  for +heap: M.Heap
  for +cx: M.Cx
  for +budget: Nat
  for +fuel: Nat
  for +root: M.T
  for +acc: M.Acc
  for +marks: List<&2, Nat>
  for +seen: List<&2, Nat>
  (M.LE(M.Ctr.reads(M.lane_ctr(heap, cx, budget, fuel, root, acc, marks, seen)),
      M.Ctr.words(M.lane_ctr(heap, cx, budget, fuel, root, acc, marks, seen)))
    & M.LE(M.Ctr.words(M.lane_ctr(heap, cx, budget, fuel, root, acc, marks, seen)),
      M.Ctr.steps(M.lane_ctr(heap, cx, budget, fuel, root, acc, marks, seen))))

# (b) a heap read: the word at i, which List.get finds (i is in range)
law heap_read:
  for +ws: List<&2, M.W>
  for +i: Nat
  for +e: M.LE(1n+i, List.length(&2, M.W, ws))
  {List.get(&2, M.W, ws, i) == Some{M.rd(M.W, ws, i, e)} : Maybe<&2, M.W>}

# (b) a table read, the same
law table_read:
  for +xs: List<&2, Nat>
  for +i: Nat
  for +e: M.LE(1n+i, List.length(&2, Nat, xs))
  {List.get(&2, Nat, xs, i) == Some{M.rd(Nat, xs, i, e)} : Maybe<&2, Nat>}

# (a) a lane ends within budget + RC_SLACK steps
law lane_ends:
  for +heap: M.Heap
  for +cx: M.Cx
  for +budget: Nat
  for +root: M.T
  for +acc: M.Acc
  for +marks: List<&2, Nat>
  for +seen: List<&2, Nat>
  {M.lane_done(heap, cx, budget, root, acc, marks, seen) == True{} : Bool}
