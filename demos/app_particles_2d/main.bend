# Particles 2D: a pure particle bang, projection/binning into cells, and a
# pure raster bang per frame. PARTICLES_BIN picks where the binning runs:
# host (default) between the two bangs; device, inside the raster bang, so
# the host never walks the world; fused, one bang a frame for all three.
# Every mode draws the same pixels. PARTICLES_SCALE selects 1024, 4096,
# 16384, 65536 (default), 262144 or 1048576 particles, a quadtree of depth 3
# to 8 with 16 per leaf. PARTICLES_PROBE=N runs N measured headless frames
# after eight warmups and prints stage medians plus deterministic checksums:
# sim, bin and raster are the clock gaps around each step (see Frame.step),
# so device puts its binning under raster (bin ~0) and fused its whole frame
# under raster (sim and bin ~0).
import Base
import ../app_slash_boss_3d/bend3d.bend as R

law Clock.us:
  IO(U32)

def Clock.us():
  import "./clock.c"

def Screen.w() -> U32:
  1024

def Screen.h() -> U32:
  768

# Named configuration definitions are passed as ~ templates to the tree
# builder and both pure stage entry points.
def Particles.k() -> Nat:
  16n

def Depth.tiny() -> Nat:
  3n

def Depth.little() -> Nat:
  4n

def Depth.small() -> Nat:
  5n

def Depth.medium() -> Nat:
  6n

def Depth.large() -> Nat:
  7n

def Depth.huge() -> Nat:
  8n

def Scale.total(~k: Nat, +depth: Nat) -> U32:
  U32.shln(U32.from_nat(k), Nat.mul(depth, 2n))

def Env.u32(m: Maybe<&2, U32>, +default: U32) -> U32:
  match m:
    case None{}:
      default
    case Some{v}:
      v

def Env.num(r: Result<&1, &1, U32 & String, String>, +default: U32) -> U32:
  match r:
    case Fail{_}:
      default
    case Done{text}:
      Env.u32(U32.read(text), default)

def Rand.next(+x: U32) -> U32:
  +a = U32.xor(x, U32.shln(x, 13n))
  +b = U32.xor(a, U32.shrn(a, 17n))
  U32.xor(b, U32.shln(b, 5n))

def Rand.unit(+x: U32) -> F32:
  (U32.to_f32((x .&. 65535 : U32)) / 65535.0 : F32)

type Particle is Data:
  Particle{x: F32, y: F32, vx: F32, vy: F32}

# Every leaf is a flat list of exactly Particles.k particles at init.
type Parts is Data:
  PNil{}
  PCons{p: Particle, rest: Parts}

type World is Data:
  WLeaf{ps: Parts}
  WQuad{tl: World, tr: World, bl: World, br: World}

def Init.parts(n: Nat, +i: U32) -> Parts:
  match n:
    case 0n:
      PNil{}
    case 1n++k:
      +j = (i + U32.from_nat(k) : U32)
      +a = Rand.next((j * 747796405 + 2891336453 : U32))
      +b = Rand.next((a + 277803737 : U32))
      +c = Rand.next((b + 1597334677 : U32))
      +d = Rand.next((c + 3812015801 : U32))
      PCons{Particle{(1.0 + Rand.unit(a) * 1022.0 : F32),
        (1.0 + Rand.unit(b) * 766.0 : F32), ((Rand.unit(c) - 0.5) * 0.34 : F32),
        ((Rand.unit(d) - 0.5) * 0.34 : F32)}, Init.parts(k, i)}

# A depth-d quadtree has 4^d leaves. Child ranges seed disjoint leaves.
def Init.tree(~k: Nat, d: Nat, +i: U32) -> World:
  match d:
    case 0n:
      WLeaf{Init.parts(k, (i * U32.from_nat(k) : U32))}
    case 1n++e:
      +stride = U32.shln(1, Nat.mul(e, 2n))
      a b c d = Init.tree(~k, e, i) Init.tree(~k, e, (i + stride : U32))
        Init.tree(~k, e, (i + stride * 2 : U32)) Init.tree(~k, e, (i + stride * 3 : U32))
      WQuad{a, b, c, d}

type Force is Data:
  Force{x: F32, y: F32}

# A softened scalar pull toward a fixed attractor.
def Pull.one(+cx: F32, +cy: F32, +strength: F32, +x: F32, +y: F32) -> Force:
  +dx = (cx - x : F32)
  +dy = (cy - y : F32)
  +r2 = (dx * dx + dy * dy + 900.0 : F32)
  +gain = (strength / r2 : F32)
  Force{(dx * gain : F32), (dy * gain : F32)}

def Wrap.at(+x: F32, +hi: F32) -> F32:
  R.pick((x < 0.0 : F32), (x + hi : F32), R.pick((x >= hi : F32), (x - hi : F32), x))

def Particle.forces(+x: F32, +y: F32, +vx: F32, +vy: F32, a: Force, b: Force) -> Particle:
  Force{ax0, ay0} = a
  Force{ax1, ay1} = b
  +nvx = ((vx + ax0 + ax1) * 0.9995 : F32)
  +nvy = ((vy + ay0 + ay1) * 0.9995 : F32)
  Particle{Wrap.at((x + nvx : F32), 1024.0), Wrap.at((y + nvy : F32), 768.0), nvx, nvy}

def Particle.step(+p: Particle) -> Particle:
  Particle{x, y, vx, vy} = p
  Particle.forces(x, y, vx, vy, Pull.one(286.0, 246.0, 2.8, x, y),
    Pull.one(758.0, 526.0, 2.1, x, y))

# The leaf kernel is a flat tail loop. Reversal is harmless because particles
# are independent and avoids a continuation frame per particle.
def Parts.move(ps: Parts, acc: Parts) -> Parts:
  match ps:
    case PNil{}:
      acc
    case PCons{p, rest}:
      Parts.move(rest, PCons{Particle.step(p), acc})

def Parts.step(ps: Parts) -> Parts:
  Parts.move(ps, PNil{})

def Sim.node(d: Nat, w: World) -> World:
  match d w:
    case 0n WLeaf{ps}:
      WLeaf{Parts.step(ps)}
    case 1n++e WQuad{tl, tr, bl, br}:
      a b c d = Sim.node(e, tl) Sim.node(e, tr) Sim.node(e, bl) Sim.node(e, br)
      WQuad{a, b, c, d}
    case _ WLeaf{ps}:
      WLeaf{Parts.step(ps)}
    case _ WQuad{tl, tr, bl, br}:
      WQuad{tl, tr, bl, br}

# The only simulation bang in a frame; depth is an erased ~ template.
def Sim.run(~depth: Nat, +w: World) -> World:
  Sim.node!(depth, w)

def Sim.d3(+w: World) -> World:
  Sim.run(~Depth.tiny, w)

def Sim.d4(+w: World) -> World:
  Sim.run(~Depth.little, w)

def Sim.d5(+w: World) -> World:
  Sim.run(~Depth.small, w)

def Sim.d6(+w: World) -> World:
  Sim.run(~Depth.medium, w)

def Sim.d7(+w: World) -> World:
  Sim.run(~Depth.large, w)

def Sim.d8(+w: World) -> World:
  Sim.run(~Depth.huge, w)

def Parts.count(ps: Parts) -> Nat:
  match ps:
    case PNil{}:
      0n
    case PCons{_, rest}:
      1n+Parts.count(rest)

def World.count(w: World) -> Nat:
  match w:
    case WLeaf{ps}:
      Parts.count(ps)
    case WQuad{tl, tr, bl, br}:
      Nat.add(Nat.add(World.count(tl), World.count(tr)),
        Nat.add(World.count(bl), World.count(br)))

# One opaque screen triangle per particle. Bend3D bins it into 64-pixel cells.
def Sprite.add(+p: Particle, c: R.Cells) -> R.Cells:
  Particle{x, y, vx, vy} = p
  +speed = R.min(1.0, ((F32.abs(vx) + F32.abs(vy)) * 3.5 : F32))
  +r = (0.22 + speed * 0.72 : F32)
  +g = (0.48 + (1.0 - speed) * 0.42 : F32)
  +b = (0.92 - speed * 0.24 : F32)
  R.Mesh.raster(R.Vert{x, (y - 1.6 : F32), 1.0, r, g, b},
    R.Vert{(x - 1.4 : F32), (y + 1.2 : F32), 1.0, r, g, b},
    R.Vert{(x + 1.4 : F32), (y + 1.2 : F32), 1.0, r, g, b}, 0, 1.0,
    1023.0, 767.0, c)

# Leaf projection/binning is a flat tail loop and only borrows ps.
def Bin.parts(+ps: Parts, c: R.Cells) -> R.Cells:
  match ps:
    case PNil{}:
      c
    case PCons{p, rest}:
      Bin.parts(rest, Sprite.add(p, c))

# Cells.m4 merges on one lane: at the root of a 262,144-particle world
# that walks every list on one lane. Pm.m2 is Cells.merge forked over k
# levels of the cell quadtree: an empty side gives the other whole, two
# quads merge child by child, anything else is Cells.merge, so the lists
# and their order are the same.
def Pm.m2(+k: Nat, a: R.Cells, b: R.Cells) -> R.Cells:
  match k a b:
    case _ R.CNil{} y:
      y
    case _ x R.CNil{}:
      x
    case 1n+e R.CQua{a1, a2, a3, a4} R.CQua{b1, b2, b3, b4}:
      p q r t = Pm.m2(e, a1, b1) Pm.m2(e, a2, b2) Pm.m2(e, a3, b3) Pm.m2(e, a4, b4)
      R.CQua{p, q, r, t}
    case _ x y:
      R.Cells.merge(x, y)

# Cells.m4's merge(merge(a, b), merge(c, d)), each merge forked.
def Pm.m4(a: R.Cells, b: R.Cells, c: R.Cells, d: R.Cells) -> R.Cells:
  x y = Pm.m2(5n, a, b) Pm.m2(5n, c, d)
  Pm.m2(5n, x, y)

def Bin.join(big: Bool, a: R.Cells, b: R.Cells, c: R.Cells, d: R.Cells) -> R.Cells:
  match big:
    case True{}:
      Pm.m4(a, b, c, d)
    case False{}:
      R.Cells.m4(a, b, c, d)

# One parallel let per recursive definition keeps binning to one fork
# frontier. It returns only cells, so the simulated world remains borrowed.
# A join forks its merge when the world is wide (65,536 and up) and its
# children hold 1,024 particles or more; below that the forks cost more
# than the lane they save (logs/fps2).
def Bin.node(+wide: Bool, d: Nat, +w: World) -> R.Cells:
  match d w:
    case 0n WLeaf{ps}:
      Bin.parts(ps, R.CNil{})
    case 1n++e WQuad{tl, tr, bl, br}:
      a b c d = Bin.node(wide, e, tl) Bin.node(wide, e, tr) Bin.node(wide, e, bl)
        Bin.node(wide, e, br)
      Bin.join(Bool.and(wide, (U32.from_nat(e) >= 3 : U32)), a, b, c, d)
    case _ WLeaf{ps}:
      Bin.parts(ps, R.CNil{})
    case _ WQuad{_, _, _, _}:
      R.CNil{}

# The cells of a frame; last frame's are freed as a branch of the build.
def Scene.build(~depth: Nat, +world: World, used: R.Cells) -> R.Cells:
  fresh gone = Bin.node((U32.from_nat(depth) >= 6 : U32), depth, world) R.Cells.drop(4n, used)
  R.Cells.merge(fresh, gone)

def Scene.d3(+world: World, used: R.Cells) -> R.Cells:
  Scene.build(~Depth.tiny, world, used)

def Scene.d4(+world: World, used: R.Cells) -> R.Cells:
  Scene.build(~Depth.little, world, used)

def Scene.d5(+world: World, used: R.Cells) -> R.Cells:
  Scene.build(~Depth.small, world, used)

def Scene.d6(+world: World, used: R.Cells) -> R.Cells:
  Scene.build(~Depth.medium, world, used)

def Scene.d7(+world: World, used: R.Cells) -> R.Cells:
  Scene.build(~Depth.large, world, used)

def Scene.d8(+world: World, used: R.Cells) -> R.Cells:
  Scene.build(~Depth.huge, world, used)

def Hook.sim() -> Type:
  @+world: World -> World

def Hook.bin() -> Type:
  @+world: World -> R.Cells -> R.Cells

# A device frame: the world, last frame's cells and image in; the new
# image, cells and world out.
def Hook.draw() -> Type:
  @+world: World -> R.Cells -> Image -> (Image & R.Cells) & World

type Sky is Data:
  Sky{}

def Sky.of(+x: U32, +y: U32, +s: U32) -> Sky:
  Sky{}

def Sky.flat(+sky: Sky, +x: U32, +y: U32, +s: U32) -> Bool:
  True{}

def Sky.col(per: Bool, +x: U32, +sky: Sky) -> Sky:
  Sky{}

def Sky.at(+x: U32, +y: U32, +sky: Sky) -> U32:
  263438

# The only raster bang in a frame. Bend3D borrows +cells, opens old, sinks
# old in the fork tree, and returns cells to the host.
def Frame.show(+cells: R.Cells, old: Image) -> Image & R.Cells:
  R.Frame.show(~Sky, ~Sky.of, ~Sky.flat, ~Sky.col, ~Sky.at, ~Screen.w, ~Screen.h, cells, old)

# Device binning (PARTICLES_BIN=device): the raster turn builds the cells
# itself, the same Scene.build the host runs, so the host never walks the
# world the sim turn wrote. Last frame's cells stay on the device: the turn
# drops them as a branch of the build. The tree is borrowed and returned,
# as in Frame.show.
def Dev.raster(+cells: R.Cells, old: Image) -> Image & R.Cells:
  (R.Frame.node(~Sky, ~Sky.of, ~Sky.flat, ~Sky.col, ~Sky.at, ~Screen.w, ~Screen.h, cells, 5n, 0,
    0, R.Image.open(old)), cells)

def Dev.build(~depth: Nat, +world: World, used: R.Cells, old: Image) -> Image & R.Cells:
  Dev.raster(Scene.build(~depth, world, used), old)

# The world is borrowed by the turn and comes back beside the image.
def Dev.run(~depth: Nat, +world: World, used: R.Cells, old: Image) -> (Image & R.Cells) & World:
  (Dev.build!(~depth, world, used, old), world)

def Dev.d3(+world: World, used: R.Cells, old: Image) -> (Image & R.Cells) & World:
  Dev.run(~Depth.tiny, world, used, old)

def Dev.d4(+world: World, used: R.Cells, old: Image) -> (Image & R.Cells) & World:
  Dev.run(~Depth.little, world, used, old)

def Dev.d5(+world: World, used: R.Cells, old: Image) -> (Image & R.Cells) & World:
  Dev.run(~Depth.small, world, used, old)

def Dev.d6(+world: World, used: R.Cells, old: Image) -> (Image & R.Cells) & World:
  Dev.run(~Depth.medium, world, used, old)

def Dev.d7(+world: World, used: R.Cells, old: Image) -> (Image & R.Cells) & World:
  Dev.run(~Depth.large, world, used, old)

def Dev.d8(+world: World, used: R.Cells, old: Image) -> (Image & R.Cells) & World:
  Dev.run(~Depth.huge, world, used, old)

# One turn a frame (PARTICLES_BIN=fused): sim, bin and raster in one bang.
def Fused.draw(~depth: Nat, +next: World, used: R.Cells, old: Image) -> (Image & R.Cells) & World:
  (Dev.build(~depth, next, used, old), next)

def Fused.build(~depth: Nat, +world: World, used: R.Cells, old: Image) -> (Image & R.Cells) & World:
  Fused.draw(~depth, Sim.node(depth, world), used, old)

def Fused.run(~depth: Nat, +world: World, used: R.Cells, old: Image) -> (Image & R.Cells) & World:
  Fused.build!(~depth, world, used, old)

def Fused.d3(+world: World, used: R.Cells, old: Image) -> (Image & R.Cells) & World:
  Fused.run(~Depth.tiny, world, used, old)

def Fused.d4(+world: World, used: R.Cells, old: Image) -> (Image & R.Cells) & World:
  Fused.run(~Depth.little, world, used, old)

def Fused.d5(+world: World, used: R.Cells, old: Image) -> (Image & R.Cells) & World:
  Fused.run(~Depth.small, world, used, old)

def Fused.d6(+world: World, used: R.Cells, old: Image) -> (Image & R.Cells) & World:
  Fused.run(~Depth.medium, world, used, old)

def Fused.d7(+world: World, used: R.Cells, old: Image) -> (Image & R.Cells) & World:
  Fused.run(~Depth.large, world, used, old)

def Fused.d8(+world: World, used: R.Cells, old: Image) -> (Image & R.Cells) & World:
  Fused.run(~Depth.huge, world, used, old)

type Sample is Data:
  Sample{sim: U32, bin: U32, raster: U32, total: U32}

type Stats is Data:
  Stats{sim: List<&2, U32>, bin: List<&2, U32>, raster: List<&2, U32>, total: List<&2, U32>}

type Mode is Data:
  BinHost{}
  BinDevice{}
  BinFused{}

def Mode.show(+m: Mode) -> String:
  match m:
    case BinHost{}:
      "host"
    case BinDevice{}:
      "device"
    case BinFused{}:
      "fused"

# One frame's world, image and cells, and its stage times.
type Step is Data:
  Step{world: World, img: Image, used: R.Cells, sample: Sample}

def Step.of(world: World, drawn: Image & R.Cells, +t0: U32, +t1: U32, +t2: U32, +t3: U32) -> Step:
  (img, used) = drawn
  Step{world, img, used, Sample{(t1 - t0 : U32), (t2 - t1 : U32), (t3 - t2 : U32),
    (t3 - t0 : U32)}}

def Step.turn(both: (Image & R.Cells) & World, +t0: U32, +t1: U32, +t2: U32, +t3: U32) -> Step:
  (drawn, world) = both
  Step.of(world, drawn, t0, t1, t2, t3)

def Stats.put(warm: Bool, +s: Sample, stats: Stats) -> Stats:
  match warm:
    case True{}:
      stats
    case False{}:
      Sample{a, b, c, d} = s
      Stats{sa, sb, sc, sd} = stats
      Stats{a <> sa, b <> sb, c <> sc, d <> sd}

def U32.le(a: U32, b: U32) -> Bool:
  (a <= b : U32)

def Median.some(m: Maybe<&2, U32>) -> U32:
  match m:
    case None{}:
      0
    case Some{x}:
      x

def Median.of(+xs: List<&2, U32>) -> U32:
  +n = List.length(&2, U32, xs)
  Median.some(List.get(&2, U32, List.sort(~U32, ~U32.le, xs), Nat.div(n, 2n)))

def Stats.report(stats: Stats) -> IO(Unit):
  Stats{a, b, c, d} = stats
  IO.print("median_us sim " ++ U32.show(Median.of(a)) ++ " bin " ++ U32.show(Median.of(b))
    ++ " raster " ++ U32.show(Median.of(c)) ++ " total " ++ U32.show(Median.of(d)))

def Hash.mix(+h: U32, +v: U32) -> U32:
  (h * 16777619 .^. v : U32)

# Coordinate-sensitive final image checksum. Quadrant salts and origin/size
# fields make a spatial permutation observable.
def Image.checksum(+img: Image, +x: U32, +y: U32, +size: U32) -> U32:
  match img:
    case Pix{c}:
      Hash.mix(Hash.mix(Hash.mix(Hash.mix(2166136261, x), y), size), c)
    case Qua{tl, tr, bl, br}:
      +h = (size >> 1n : U32)
      a b c d = Image.checksum(tl, x, y, h) Image.checksum(tr, (x + h : U32), y, h)
        Image.checksum(bl, x, (y + h : U32), h)
        Image.checksum(br, (x + h : U32), (y + h : U32), h)
      Hash.mix(Hash.mix(Hash.mix(Hash.mix(a, (b .^. 2654435769 : U32)),
        (c .^. 2246822519 : U32)), (d .^. 3266489917 : U32)), size)

def Parts.checksum(ps: Parts, +h: U32) -> U32:
  match ps:
    case PNil{}:
      h
    case PCons{Particle{x, y, vx, vy}, rest}:
      Parts.checksum(rest, Hash.mix(Hash.mix(Hash.mix(Hash.mix(h, F32.bits(x)),
        F32.bits(y)), F32.bits(vx)), F32.bits(vy)))

def World.checksum(w: World) -> U32:
  match w:
    case WLeaf{ps}:
      Parts.checksum(ps, 2166136261)
    case WQuad{tl, tr, bl, br}:
      a b c d = World.checksum(tl) World.checksum(tr) World.checksum(bl) World.checksum(br)
      Hash.mix(Hash.mix(Hash.mix(a, (b .^. 2654435769 : U32)),
        (c .^. 2246822519 : U32)), (d .^. 3266489917 : U32))

def Probe.lines(stats: Stats, +pixels: U32, +state: U32) -> IO(Unit):
  do IO<Unit>:
    Unit <- Stats.report(stats)
    IO.print("checksum pixels " ++ U32.show(pixels) ++ " state " ++ U32.show(state))

def Probe.report(stats: Stats, +pixels: U32, +state: U32, gone: R.Cells) -> IO(Unit):
  match gone:
    case R.CNil{}:
      Probe.lines(stats, pixels, state)
    case R.CLeaf{_, _}:
      Probe.lines(stats, pixels, state)
    case R.CQua{_, _, _, _}:
      Probe.lines(stats, pixels, state)

def Probe.finish(stats: Stats, world: World, img: Image, used: R.Cells) -> IO(Unit):
  Probe.report(stats, Image.checksum(img, 0, 0, 2048), World.checksum(world),
    R.Cells.drop(4n, used))

# One frame. Clock effects delimit the stages; no bang appears directly in
# a do continuation. host: sim turn | host bin | raster turn. device: sim
# turn | nothing (bin ~0) | bin + raster turn. fused: nothing | nothing |
# one sim + bin + raster turn.
def Frame.step(
  ~sim: Hook.sim(), ~bin: Hook.bin(), ~dev: Hook.draw(), ~fused: Hook.draw(), +mode: Mode,
  world: World, used: R.Cells, old: Image
) -> IO(Step):
  match mode:
    case BinHost{}:
      do IO<Step>:
        +t0 : U32 <- Clock.us()
        +next : World <- IO.pure(World, sim(world))
        +t1 : U32 <- Clock.us()
        cells : R.Cells = bin(next, used)
        +t2 : U32 <- Clock.us()
        drawn : Image & R.Cells <- IO.pure(Image & R.Cells, Frame.show(cells, old))
        +t3 : U32 <- Clock.us()
        IO.pure(Step, Step.of(next, drawn, t0, t1, t2, t3))
    case BinDevice{}:
      do IO<Step>:
        +t0 : U32 <- Clock.us()
        +next : World <- IO.pure(World, sim(world))
        +t1 : U32 <- Clock.us()
        +t2 : U32 <- Clock.us()
        both : (Image & R.Cells) & World <- IO.pure((Image & R.Cells) & World, dev(next, used, old))
        +t3 : U32 <- Clock.us()
        IO.pure(Step, Step.turn(both, t0, t1, t2, t3))
    case BinFused{}:
      do IO<Step>:
        +t0 : U32 <- Clock.us()
        +t1 : U32 <- Clock.us()
        +t2 : U32 <- Clock.us()
        both : (Image & R.Cells) & World <- IO.pure((Image & R.Cells) & World, fused(world, used, old))
        +t3 : U32 <- Clock.us()
        IO.pure(Step, Step.turn(both, t0, t1, t2, t3))

# The state holds the last frame's sample: frame 0's is a placeholder,
# and it and the first eight frames are warmups.
def Probe.loop(
  ~sim: Hook.sim(), ~bin: Hook.bin(), ~dev: Hook.draw(), ~fused: Hook.draw(), +mode: Mode,
  left: Nat, +frame: U32, now: Step, stats: Stats
) -> IO(Unit):
  match left:
    case 0n:
      Step{world, old, used, sample} = now
      Probe.finish(Stats.put((frame < 9 : U32), sample, stats), world, old, used)
    case 1n+k:
      Step{world, old, used, sample} = now
      do IO<Unit>:
        next : Step <- Frame.step(~sim, ~bin, ~dev, ~fused, mode, world, used, old)
        Probe.loop(~sim, ~bin, ~dev, ~fused, mode, k, (frame + 1 : U32), next,
          Stats.put((frame < 9 : U32), sample, stats))

def Probe.run(
  ~depth: Nat, ~sim: Hook.sim(), ~bin: Hook.bin(), ~dev: Hook.draw(), ~fused: Hook.draw(),
  +mode: Mode, +frames: U32
) -> IO(Unit):
  +particles = Scale.total(~Particles.k, depth)
  do IO<Unit>:
    Unit <- IO.print("particles=" ++ U32.show(particles) ++ " frames=" ++ U32.show(frames)
      ++ " warmup=8")
    Unit <- IO.print("bin=" ++ Mode.show(mode))
    Probe.loop(~sim, ~bin, ~dev, ~fused, mode, Nat.add(U32.to_nat(frames), 8n), 0,
      Step{Init.tree(~Particles.k, depth, 0), Pix{0}, R.CNil{}, Sample{0, 0, 0, 0}},
      Stats{Nil{}, Nil{}, Nil{}, Nil{}})

type Live is Type:
  Live{world: World, used: R.Cells, window: Window, old: Image, events: List<Event>}

def Play.pack(world: World, used: R.Cells, shown: Window & Image & List<Event>) -> Live:
  (window, image, events) = shown
  Live{world, used, window, image, events}

def Play.present(window: Window, step: Step) -> IO(Live):
  Step{world, img, retained, _} = step
  do IO<Live>:
    shown : Window & Image & List<Event> <- Window.frame(window, img)
    IO.pure(Live, Play.pack(world, retained, shown))

@unsafe
def Play.loop(
  ~sim: Hook.sim(), ~bin: Hook.bin(), ~dev: Hook.draw(), ~fused: Hook.draw(), +mode: Mode,
  live: Live
) -> IO(Unit):
  Live{world, used, window, old, events} = live
  match events:
    case Key{27, True{}} <> rest:
      Window.close(window)
    case Close{} <> rest:
      Window.close(window)
    case _ <> rest:
      Play.loop(~sim, ~bin, ~dev, ~fused, mode, Live{world, used, window, old, rest})
    case Nil{}:
      do IO<Unit>:
        step : Step <- Frame.step(~sim, ~bin, ~dev, ~fused, mode, world, used, old)
        next_live : Live <- Play.present(window, step)
        Play.loop(~sim, ~bin, ~dev, ~fused, mode, next_live)

def Play.run(
  ~depth: Nat, ~sim: Hook.sim(), ~bin: Hook.bin(), ~dev: Hook.draw(), ~fused: Hook.draw(),
  +mode: Mode
) -> IO(Unit):
  do IO<Unit>:
    window : Window <- IO.try(Window, Window.open("Particles 2D", Screen.w(), Screen.h()))
    Play.loop(~sim, ~bin, ~dev, ~fused, mode,
      Live{Init.tree(~Particles.k, depth, 0), R.CNil{}, window, Pix{0}, Nil{}})

def Main.mode(
  ~depth: Nat, ~sim: Hook.sim(), ~bin: Hook.bin(), ~dev: Hook.draw(), ~fused: Hook.draw(),
  +mode: Mode, probe: Result<&1, &1, U32 & String, String>
) -> IO(Unit):
  match probe:
    case Fail{_}:
      Play.run(~depth, ~sim, ~bin, ~dev, ~fused, mode)
    case Done{text}:
      Probe.run(~depth, ~sim, ~bin, ~dev, ~fused, mode, Env.u32(U32.read(text), 120))

# The first flag set picks its depth; none picks the default, depth 6.
def Main.scale(
  tiny: Bool, little: Bool, small: Bool, large: Bool, huge: Bool, +mode: Mode,
  probe: Result<&1, &1, U32 & String, String>
) -> IO(Unit):
  match tiny little small large huge:
    case True{} _ _ _ _:
      Main.mode(~Depth.tiny, ~Sim.d3, ~Scene.d3, ~Dev.d3, ~Fused.d3, mode,
        probe)
    case _ True{} _ _ _:
      Main.mode(~Depth.little, ~Sim.d4, ~Scene.d4, ~Dev.d4, ~Fused.d4, mode,
        probe)
    case _ _ True{} _ _:
      Main.mode(~Depth.small, ~Sim.d5, ~Scene.d5, ~Dev.d5, ~Fused.d5, mode,
        probe)
    case _ _ _ True{} _:
      Main.mode(~Depth.large, ~Sim.d7, ~Scene.d7, ~Dev.d7, ~Fused.d7, mode,
        probe)
    case _ _ _ _ True{}:
      Main.mode(~Depth.huge, ~Sim.d8, ~Scene.d8, ~Dev.d8, ~Fused.d8, mode,
        probe)
    case _ _ _ _ _:
      Main.mode(~Depth.medium, ~Sim.d6, ~Scene.d6, ~Dev.d6, ~Fused.d6, mode,
        probe)

# PARTICLES_BIN: host (default), device or fused; anything else is host.
def Mode.pick(device: Bool, fused: Bool) -> Mode:
  match device fused:
    case True{} _:
      BinDevice{}
    case _ True{}:
      BinFused{}
    case _ _:
      BinHost{}

def Mode.of(r: Result<&1, &1, U32 & String, String>) -> Mode:
  match r:
    case Fail{_}:
      BinHost{}
    case Done{+text}:
      Mode.pick(String.eq(text, "device"), String.eq(text, "fused"))

def main() -> IO(Unit):
  do IO<Unit>:
    scale_env : Result<&1, &1, U32 & String, String> <- IO.get_env("PARTICLES_SCALE")
    probe : Result<&1, &1, U32 & String, String> <- IO.get_env("PARTICLES_PROBE")
    bin_env : Result<&1, &1, U32 & String, String> <- IO.get_env("PARTICLES_BIN")
    +scale : U32 = Env.num(scale_env, 65536)
    Main.scale(U32.is_eq(scale, 1024), U32.is_eq(scale, 4096), U32.is_eq(scale, 16384),
      U32.is_eq(scale, 262144), U32.is_eq(scale, 1048576), Mode.of(bin_env), probe)
