# Particles 2D: a pure particle bang, host projection/binning, and a pure
# raster bang per frame. PARTICLES_SCALE selects 1024, 4096, 16384, 65536
# (default), 262144 or 1048576 particles, a quadtree of depth 3 to 8 with 16
# per leaf. PARTICLES_PROBE=N runs N measured headless frames after eight
# warmups and prints stage medians plus deterministic checksums.
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

# Host leaf projection/binning is a flat tail loop and only borrows ps.
def Bin.parts(+ps: Parts, c: R.Cells) -> R.Cells:
  match ps:
    case PNil{}:
      c
    case PCons{p, rest}:
      Bin.parts(rest, Sprite.add(p, c))

# One parallel let per recursive definition keeps host binning to one fork
# frontier. It returns only cells, so the simulated world remains borrowed.
def Bin.node(d: Nat, +w: World) -> R.Cells:
  match d w:
    case 0n WLeaf{ps}:
      Bin.parts(ps, R.CNil{})
    case 1n++e WQuad{tl, tr, bl, br}:
      a b c d = Bin.node(e, tl) Bin.node(e, tr) Bin.node(e, bl) Bin.node(e, br)
      R.Cells.m4(a, b, c, d)
    case _ WLeaf{ps}:
      Bin.parts(ps, R.CNil{})
    case _ WQuad{_, _, _, _}:
      R.CNil{}

def Scene.build(~depth: Nat, +world: World, used: R.Cells) -> R.Cells:
  fresh gone = Bin.node(depth, world) R.Cells.drop(4n, used)
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

type Sample is Data:
  Sample{sim: U32, bin: U32, raster: U32, total: U32}

type Stats is Data:
  Stats{sim: List<&2, U32>, bin: List<&2, U32>, raster: List<&2, U32>, total: List<&2, U32>}

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

# Clock effects delimit the pure simulation bang, host bin, and pure raster
# bang. No bang appears directly in this do continuation.
def Probe.loop(
  ~sim: Hook.sim(), ~bin: Hook.bin(), left: Nat, +frame: U32, world: World,
  last: Image & R.Cells, stats: Stats
) -> IO(Unit):
  match left:
    case 0n:
      (old, used) = last
      Probe.finish(stats, world, old, used)
    case 1n+k:
      (old, used) = last
      do IO<Unit>:
        +t0 : U32 <- Clock.us()
        +next : World <- IO.pure(World, sim(world))
        +t1 : U32 <- Clock.us()
        cells : R.Cells = bin(next, used)
        +t2 : U32 <- Clock.us()
        drawn : Image & R.Cells <- IO.pure(Image & R.Cells, Frame.show(cells, old))
        +t3 : U32 <- Clock.us()
        sample : Sample = {Sample{(t1 - t0 : U32), (t2 - t1 : U32),
          (t3 - t2 : U32), (t3 - t0 : U32)} : Sample}
        Probe.loop(~sim, ~bin, k, (frame + 1 : U32), next, drawn,
          Stats.put((frame < 8 : U32), sample, stats))

def Probe.run(~depth: Nat, ~sim: Hook.sim(), ~bin: Hook.bin(), +frames: U32) -> IO(Unit):
  +particles = Scale.total(~Particles.k, depth)
  do IO<Unit>:
    Unit <- IO.print("particles=" ++ U32.show(particles) ++ " frames=" ++ U32.show(frames)
      ++ " warmup=8")
    Probe.loop(~sim, ~bin, Nat.add(U32.to_nat(frames), 8n), 0,
      Init.tree(~Particles.k, depth, 0), (Pix{0}, R.CNil{}), Stats{Nil{}, Nil{}, Nil{}, Nil{}})

type Live is Type:
  Live{world: World, used: R.Cells, window: Window, old: Image, events: List<Event>}

def Play.pack(world: World, used: R.Cells, shown: Window & Image & List<Event>) -> Live:
  (window, image, events) = shown
  Live{world, used, window, image, events}

def Play.present(window: Window, world: World, drawn: Image & R.Cells) -> IO(Live):
  (img, retained) = drawn
  do IO<Live>:
    shown : Window & Image & List<Event> <- Window.frame(window, img)
    IO.pure(Live, Play.pack(world, retained, shown))

@unsafe
def Play.loop(~sim: Hook.sim(), ~bin: Hook.bin(), live: Live) -> IO(Unit):
  Live{world, used, window, old, events} = live
  match events:
    case Key{27, True{}} <> rest:
      Window.close(window)
    case Close{} <> rest:
      Window.close(window)
    case _ <> rest:
      Play.loop(~sim, ~bin, Live{world, used, window, old, rest})
    case Nil{}:
      do IO<Unit>:
        before : U32 <- Clock.us()
        +next : World <- IO.pure(World, sim(world))
        after_sim : U32 <- Clock.us()
        cells : R.Cells = bin(next, used)
        after_bin : U32 <- Clock.us()
        drawn : Image & R.Cells <- IO.pure(Image & R.Cells, Frame.show(cells, old))
        next_live : Live <- Play.present(window, next, drawn)
        Play.loop(~sim, ~bin, next_live)

def Play.run(~depth: Nat, ~sim: Hook.sim(), ~bin: Hook.bin()) -> IO(Unit):
  do IO<Unit>:
    window : Window <- IO.try(Window, Window.open("Particles 2D", Screen.w(), Screen.h()))
    Play.loop(~sim, ~bin,
      Live{Init.tree(~Particles.k, depth, 0), R.CNil{}, window, Pix{0}, Nil{}})

def Main.mode(
  ~depth: Nat, ~sim: Hook.sim(), ~bin: Hook.bin(), probe: Result<&1, &1, U32 & String, String>
) -> IO(Unit):
  match probe:
    case Fail{_}:
      Play.run(~depth, ~sim, ~bin)
    case Done{text}:
      Probe.run(~depth, ~sim, ~bin, Env.u32(U32.read(text), 120))

# The first flag set picks its depth; none picks the default, depth 6.
def Main.scale(
  tiny: Bool, little: Bool, small: Bool, large: Bool, huge: Bool,
  probe: Result<&1, &1, U32 & String, String>
) -> IO(Unit):
  match tiny little small large huge:
    case True{} _ _ _ _:
      Main.mode(~Depth.tiny, ~Sim.d3, ~Scene.d3, probe)
    case _ True{} _ _ _:
      Main.mode(~Depth.little, ~Sim.d4, ~Scene.d4, probe)
    case _ _ True{} _ _:
      Main.mode(~Depth.small, ~Sim.d5, ~Scene.d5, probe)
    case _ _ _ True{} _:
      Main.mode(~Depth.large, ~Sim.d7, ~Scene.d7, probe)
    case _ _ _ _ True{}:
      Main.mode(~Depth.huge, ~Sim.d8, ~Scene.d8, probe)
    case _ _ _ _ _:
      Main.mode(~Depth.medium, ~Sim.d6, ~Scene.d6, probe)

def main() -> IO(Unit):
  do IO<Unit>:
    scale_env : Result<&1, &1, U32 & String, String> <- IO.get_env("PARTICLES_SCALE")
    probe : Result<&1, &1, U32 & String, String> <- IO.get_env("PARTICLES_PROBE")
    +scale : U32 = Env.num(scale_env, 65536)
    Main.scale(U32.is_eq(scale, 1024), U32.is_eq(scale, 4096), U32.is_eq(scale, 16384),
      U32.is_eq(scale, 262144), U32.is_eq(scale, 1048576), probe)
