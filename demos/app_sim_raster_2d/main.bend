# Particles 2D: two GPU bangs per frame. The first advances 16,384
# independent leaf-local particle systems; the host then turns the actual
# positions into per-cell sprite triangles; the second bang rasterizes them.
# PARTICLES_SCALE is 16384, 65536 (default), or 262144. PARTICLES_PROBE=N
# runs headless, ignores the first eight frames, prints samples, medians and
# deterministic final pixel/state checksums.
import Base
import ../app_slash_boss_3d/bend3d.bend as R

def Clock.us() -> IO(Nat):
  import "./timing.c"

def Screen.w() -> U32:
  1024

def Screen.h() -> U32:
  768

# One source-level knob for both the simulation fork tree and initial world.
# Depth 7 gives 4^7 = 16,384 independent leaf-local systems.
def Config.depth() -> Nat:
  7n

def Config.small() -> Nat:
  1n

def Config.medium() -> Nat:
  4n

def Config.large() -> Nat:
  16n

def Scale.parts.go(a: Bool, b: Bool) -> Nat:
  match a b:
    case True{} _:
      Config.small()
    case _ True{}:
      Config.large()
    case _ _:
      Config.medium()

def Scale.parts(+n: U32) -> Nat:
  Scale.parts.go(U32.is_eq(n, 16384), U32.is_eq(n, 262144))

def Scale.leaves(d: Nat) -> U32:
  match d:
    case 0n:
      1
    case 1n+k:
      (4 * Scale.leaves(k) : U32)

def Scale.total(+n: U32) -> U32:
  (Scale.leaves(Config.depth()) * U32.from_nat(Scale.parts(n)) : U32)

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

type Parts is Data:
  PNil{}
  PCons{p: Particle, rest: Parts}

type World is Data:
  WLeaf{ps: Parts}
  WQua{tl: World, tr: World, bl: World, br: World}

def Init.parts(+n: Nat, +lx: U32, +ly: U32, +seed: U32) -> Parts:
  match n:
    case 0n:
      PNil{}
    case 1n+k:
      +a = Rand.next((seed + U32.from_nat(k) * 747796405 : U32))
      +b = Rand.next((a + 2891336453 : U32))
      +c = Rand.next((b + 277803737 : U32))
      +fx = (U32.to_f32((lx * 8 + 1 : U32)) + Rand.unit(a) * 6.0 : F32)
      +fy = (U32.to_f32((ly * 6 + 1 : U32)) + Rand.unit(b) * 4.0 : F32)
      +vx = ((Rand.unit(c) - 0.5) * 0.24 : F32)
      +vy = ((Rand.unit(Rand.next(c)) - 0.5) * 0.24 : F32)
      PCons{Particle{fx, fy, vx, vy}, Init.parts(k, lx, ly, b)}

def Init.tree(~count: Nat, +d: Nat, +lx: U32, +ly: U32) -> World:
  match d:
    case 0n:
      WLeaf{Init.parts(count, lx, ly, (lx * 2246822519 + ly * 3266489917 + 1 : U32))}
    case 1n+e:
      +h = U32.shln(1, e)
      a b c d = Init.tree(~count, e, lx, ly) Init.tree(~count, e, (lx + h : U32), ly)
        Init.tree(~count, e, lx, (ly + h : U32))
        Init.tree(~count, e, (lx + h : U32), (ly + h : U32))
      WQua{a, b, c, d}

def World.init.go(~depth: Nat, a: Bool, b: Bool) -> World:
  match a b:
    case True{} _:
      Init.tree(~Config.small(), depth, 0, 0)
    case _ True{}:
      Init.tree(~Config.large(), depth, 0, 0)
    case _ _:
      Init.tree(~Config.medium(), depth, 0, 0)

def World.init(~depth: Nat, +scale: U32) -> World:
  World.init.go(~depth, U32.is_eq(scale, 16384), U32.is_eq(scale, 262144))

def Sim.one(+cx: F32, +cy: F32, +p: Particle) -> Particle:
  Particle{x, y, vx, vy} = p
  +dx = (cx - x : F32)
  +dy = (cy - y : F32)
  +r2 = (dx * dx + dy * dy + 0.35 : F32)
  +inv = (1.0 / F32.sqrt(r2) : F32)
  +pull = (0.018 * inv * inv * inv : F32)
  +nvx = ((vx + dx * pull) * 0.9992 : F32)
  +nvy = ((vy + dy * pull) * 0.9992 : F32)
  Particle{(x + nvx : F32), (y + nvy : F32), nvx, nvy}

def Sim.parts.go(ps: Parts, +cx: F32, +cy: F32, acc: Parts) -> Parts:
  match ps:
    case PNil{}:
      acc
    case PCons{p, rest}:
      Sim.parts.go(rest, cx, cy, PCons{Sim.one(cx, cy, p), acc})

def Sim.parts(ps: Parts, +cx: F32, +cy: F32) -> Parts:
  Sim.parts.go(ps, cx, cy, PNil{})

def Sim.tree(+d: Nat, w: World, +lx: U32, +ly: U32) -> World:
  match d w:
    case 0n WLeaf{ps}:
      WLeaf{Sim.parts(ps, U32.to_f32((lx * 8 + 4 : U32)),
        U32.to_f32((ly * 6 + 3 : U32)))}
    case 1n+e WQua{tl, tr, bl, br}:
      +h = U32.shln(1, e)
      a b c d = Sim.tree(e, tl, lx, ly) Sim.tree(e, tr, (lx + h : U32), ly)
        Sim.tree(e, bl, lx, (ly + h : U32)) Sim.tree(e, br, (lx + h : U32), (ly + h : U32))
      WQua{a, b, c, d}
    case _ WLeaf{ps}:
      WLeaf{ps}
    case _ WQua{tl, tr, bl, br}:
      WQua{tl, tr, bl, br}

def Sim.run(~depth: Nat, w: World) -> World:
  Sim.tree!(depth, w, 0, 0)

def Sprite.color(+vx: F32, +vy: F32) -> R.Vec:
  +speed = R.min(1.0, ((F32.abs(vx) + F32.abs(vy)) * 3.5 : F32))
  R.Vec{(0.22 + speed * 0.72 : F32), (0.48 + (1.0 - speed) * 0.42 : F32),
    (0.92 - speed * 0.24 : F32)}

def Sprite.add.go(+x: F32, +y: F32, +color: R.Vec, c: R.Cells) -> R.Cells:
  R.Vec{r, g, b} = color
  +s = {1.35 : F32}
  +tl = {R.Vert{(x - s : F32), (y - s : F32), 1.0, r, g, b} : R.Vert}
  +tr = {R.Vert{(x + s : F32), (y - s : F32), 1.0, r, g, b} : R.Vert}
  +bl = {R.Vert{(x - s : F32), (y + s : F32), 1.0, r, g, b} : R.Vert}
  +br = {R.Vert{(x + s : F32), (y + s : F32), 1.0, r, g, b} : R.Vert}
  R.Mesh.raster(tl, bl, br, 0, 1.0, 1023.0, 767.0,
    R.Mesh.raster(tl, br, tr, 0, 1.0, 1023.0, 767.0, c))

def Sprite.add(+x: F32, +y: F32, +vx: F32, +vy: F32, c: R.Cells) -> R.Cells:
  Sprite.add.go(x, y, Sprite.color(vx, vy), c)

def Scene.parts.go(ps: Parts, out: Parts, c: R.Cells) -> Parts & R.Cells:
  match ps:
    case PNil{}:
      (out, c)
    case PCons{Particle{+x, +y, +vx, +vy}, rest}:
      Scene.parts.go(rest, PCons{Particle{x, y, vx, vy}, out}, Sprite.add(x, y, vx, vy, c))

def Scene.parts(ps: Parts, c: R.Cells) -> Parts & R.Cells:
  Scene.parts.go(ps, PNil{}, c)

def Scene.leaf(pair: Parts & R.Cells) -> World & R.Cells:
  (out, cells) = pair
  (WLeaf{out}, cells)

def Scene.quad(
  a: World & R.Cells, b: World & R.Cells, c: World & R.Cells, d: World & R.Cells
) -> World & R.Cells:
  (wa, ca) = a
  (wb, cb) = b
  (wc, cc) = c
  (wd, cd) = d
  (WQua{wa, wb, wc, wd}, R.Cells.m4(ca, cb, cc, cd))

def Scene.tree(w: World) -> World & R.Cells:
  match w:
    case WLeaf{ps}:
      Scene.leaf(Scene.parts(ps, R.CNil{}))
    case WQua{tl, tr, bl, br}:
      a b c d = Scene.tree(tl) Scene.tree(tr) Scene.tree(bl) Scene.tree(br)
      Scene.quad(a, b, c, d)

def Scene.done(fresh: World & R.Cells, gone: R.Cells) -> World & R.Cells:
  (next, cells) = fresh
  (next, R.Cells.merge(cells, gone))

def Scene.build(w: World, used: R.Cells) -> World & R.Cells:
  fresh gone = Scene.tree(w) R.Cells.drop(4n, used)
  Scene.done(fresh, gone)

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

def Frame.show(+cells: R.Cells, old: Image) -> Image & R.Cells:
  R.Frame.show(~Sky, ~Sky.of, ~Sky.flat, ~Sky.col, ~Sky.at, ~Screen.w, ~Screen.h, cells, old)

def Clock.delta(+a: Nat, +b: Nat) -> U32:
  U32.from_nat(Nat.sub(b, a))

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

def Hash.four(a: U32, b: U32, c: U32, d: U32) -> U32:
  Hash.mix(Hash.mix(Hash.mix(a, b), c), d)

# Hash logical pixels in quadrant order, independent of Pix compression.
# A compressed square hashes exactly like four equal smaller squares.
def Image.uniform(d: Nat, +color: U32) -> U32:
  match d:
    case 0n:
      Hash.mix(2166136261, color)
    case 1n+k:
      +h = Image.uniform(k, color)
      Hash.four(h, h, h, h)

def Image.checksum(+d: Nat, img: Image) -> U32:
  match d img:
    case _ Pix{c}:
      Image.uniform(d, c)
    case 0n Qua{tl, tr, bl, br}:
      Hash.four(Image.checksum(0n, tl), Image.checksum(0n, tr),
        Image.checksum(0n, bl), Image.checksum(0n, br))
    case 1n+k Qua{tl, tr, bl, br}:
      a b c d = Image.checksum(k, tl) Image.checksum(k, tr)
        Image.checksum(k, bl) Image.checksum(k, br)
      Hash.four(a, b, c, d)

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
    case WQua{tl, tr, bl, br}:
      a b c d = World.checksum(tl) World.checksum(tr) World.checksum(bl) World.checksum(br)
      Hash.mix(Hash.mix(Hash.mix(a, b), c), d)

def Probe.say(+i: U32, +s: Sample) -> IO(Unit):
  Sample{a, b, c, d} = s
  IO.print("frame " ++ U32.show(i) ++ " sim_us " ++ U32.show(a) ++ " bin_us "
    ++ U32.show(b) ++ " raster_us " ++ U32.show(c) ++ " total_us " ++ U32.show(d))

def Probe.finish(+frames: U32, +particles: U32, stats: Stats, world: World, img: Image) -> IO(Unit):
  +pixels = Image.checksum(11n, img)
  +state = World.checksum(world)
  do IO<Unit>:
    Unit <- Stats.report(stats)
    Unit <- IO.print("checksum pixels " ++ U32.show(pixels) ++ " state " ++ U32.show(state))
    IO.print("frames " ++ U32.show(frames) ++ " warmup 8 particles " ++ U32.show(particles))

def Probe.line(on: Bool, +i: U32, +s: Sample) -> IO(Unit):
  match on:
    case True{}:
      Probe.say(i, s)
    case False{}:
      IO.pure(Unit, Unit{})

def Probe.after(
  +frame: U32, kept: World, drawn: Image & R.Cells, stats: Stats,
  +t0: Nat, +t1: Nat, +t2: Nat, +t3: Nat,
  rest: World -> Image -> R.Cells -> Stats -> IO(Unit)
) -> IO(Unit):
  (img, retained) = drawn
  +sample = {Sample{Clock.delta(t0, t1), Clock.delta(t1, t2), Clock.delta(t2, t3),
    Clock.delta(t0, t3)} : Sample}
  do IO<Unit>:
    Unit <- Probe.line((frame >= 8 : U32), frame, sample)
    rest(kept, img, retained, Stats.put((frame < 8 : U32), sample, stats))

def Probe.raster(
  +frame: U32, built: World & R.Cells, old: Image, stats: Stats,
  +t0: Nat, +t1: Nat, +t2: Nat,
  rest: World -> Image -> R.Cells -> Stats -> IO(Unit)
) -> IO(Unit):
  (kept, cells) = built
  do IO<Unit>:
    drawn : Image & R.Cells <- IO.pure(Image & R.Cells, Frame.show(cells, old))
    t3 : Nat <- Clock.us()
    Probe.after(frame, kept, drawn, stats, t0, t1, t2, t3, rest)

def Probe.loop(
  left: Nat, +frame: U32, +frames: U32, +particles: U32, world: World, old: Image,
  used: R.Cells, stats: Stats
) -> IO(Unit):
  match left:
    case 0n:
      Probe.finish(frames, particles, stats, world, old)
    case 1n+k:
      do IO<Unit>:
        t0 : Nat <- Clock.us()
        next : World <- IO.pure(World, Sim.run(~Config.depth(), world))
        seam1 : Nat <- IO.now()
        t1 : Nat <- Clock.us()
        built : World & R.Cells = Scene.build(next, used)
        seam2 : Nat <- IO.now()
        t2 : Nat <- Clock.us()
        Probe.raster(frame, built, old, stats, t0, t1, t2,
          w => i => c => s => Probe.loop(k, (frame + 1 : U32), frames, particles, w, i, c, s))

def Probe.run(+frames: U32, +scale: U32) -> IO(Unit):
  +particles = Scale.total(scale)
  Probe.loop(U32.to_nat(frames), 0, frames, particles, World.init(~Config.depth(), scale),
    Pix{0}, R.CNil{}, Stats{Nil{}, Nil{}, Nil{}, Nil{}})

def Play.events(events: List<Event>) -> Bool:
  match events:
    case Nil{}:
      True{}
    case Key{27, True{}} <> rest:
      False{}
    case Close{} <> rest:
      False{}
    case _ <> rest:
      Play.events(rest)

def Play.next(
  go: Bool, window: Window, world: World, old: Image, used: R.Cells,
  rest: Window -> World -> Image -> R.Cells -> IO(Unit)
) -> IO(Unit):
  match go:
    case False{}:
      Window.close(window)
    case True{}:
      rest(window, world, old, used)

def Play.shown(
  world: World, used: R.Cells, tr: Image, bl: Image, br: Image,
  shown: Window & Image & List<Event>,
  rest: Window -> World -> Image -> R.Cells -> IO(Unit)
) -> IO(Unit):
  (win, image, events) = shown
  Play.next(Play.events(events), win, world, Qua{image, tr, bl, br}, used, rest)

def Play.open(
  window: Window, world: World, used: R.Cells, four: R.Four,
  rest: Window -> World -> Image -> R.Cells -> IO(Unit)
) -> IO(Unit):
  R.Four{tl, tr, bl, br} = four
  do IO<Unit>:
    shown : Window & Image & List<Event> <- Window.frame(window, tl)
    Play.shown(world, used, tr, bl, br, shown, rest)

def Play.blit(
  window: Window, world: World, drawn: Image & R.Cells,
  rest: Window -> World -> Image -> R.Cells -> IO(Unit)
) -> IO(Unit):
  (img, retained) = drawn
  Play.open(window, world, retained, R.Image.open(img), rest)

def Play.raster(
  window: Window, built: World & R.Cells, old: Image,
  rest: Window -> World -> Image -> R.Cells -> IO(Unit)
) -> IO(Unit):
  (kept, cells) = built
  do IO<Unit>:
    drawn : Image & R.Cells <- IO.pure(Image & R.Cells, Frame.show(cells, old))
    Play.blit(window, kept, drawn, rest)

@unsafe
def Play.loop(window: Window, world: World, old: Image, used: R.Cells) -> IO(Unit):
  do IO<Unit>:
    next : World <- IO.pure(World, Sim.run(~Config.depth(), world))
    seam1 : Nat <- IO.now()
    built : World & R.Cells = Scene.build(next, used)
    seam2 : Nat <- IO.now()
    Play.raster(window, built, old,
      w => s => i => c => Play.loop(w, s, i, c))

def Play.run(+scale: U32) -> IO(Unit):
  do IO<Unit>:
    window : Window <- IO.try(Window, Window.open("Sim + Raster (two turns)", Screen.w(), Screen.h()))
    world : World = World.init(~Config.depth(), scale)
    seam : Nat <- IO.now()
    Play.loop(window, world, Pix{0}, R.CNil{})

def Main.mode(probe: Result<&1, &1, U32 & String, String>, +scale: U32) -> IO(Unit):
  match probe:
    case Fail{_}:
      Play.run(scale)
    case Done{text}:
      Probe.run(Env.u32(U32.read(text), 120), scale)

def main() -> IO(Unit):
  do IO<Unit>:
    scale_env : Result<&1, &1, U32 & String, String> <- IO.get_env("PARTICLES_SCALE")
    probe : Result<&1, &1, U32 & String, String> <- IO.get_env("PARTICLES_PROBE")
    Main.mode(probe, Env.num(scale_env, 65536))
