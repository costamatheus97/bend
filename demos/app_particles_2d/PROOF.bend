# Particles -- proof that the flat leaf loop and the parallel tree step
# preserve particle count.
import Base
import ./main.bend as App
import ./LAWS.bend as Laws

def add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def move_count(ps: App.Parts, +acc: App.Parts)
  -> {App.Parts.count(App.Parts.move(ps, acc)) == Nat.add(App.Parts.count(ps), App.Parts.count(acc)) : Nat}:
  match ps:
    case App.PNil{}:
      {==}
    case App.PCons{+p, +rest}:
      Equal.trans(Nat,
        App.Parts.count(App.Parts.move(rest, App.PCons{App.Particle.step(p), acc})),
        Nat.add(App.Parts.count(rest), 1n+App.Parts.count(acc)),
        1n+Nat.add(App.Parts.count(rest), App.Parts.count(acc)),
        move_count(rest, App.PCons{App.Particle.step(p), acc}),
        add_succ(App.Parts.count(rest), App.Parts.count(acc)))

def Laws.step_parts_count(ps):
  Equal.trans(Nat,
    App.Parts.count(App.Parts.move(ps, App.PNil{})),
    Nat.add(App.Parts.count(ps), 0n),
    App.Parts.count(ps),
    move_count(ps, App.PNil{}),
    add_zero(App.Parts.count(ps)))

def Laws.step_world_count(depth, world):
  match depth world:
    case 0n App.WLeaf{ps}:
      Laws.step_parts_count(ps)
    case 1n++e App.WQuad{a, b, c, d}:
      %Laws.step_world_count(e, a)
        : {App.World.count(App.Sim.node(1n+e, App.WQuad{a, b, c, d}))
          == Nat.add(Nat.add(_, App.World.count(b)),
            Nat.add(App.World.count(c), App.World.count(d))) : Nat}
      %Laws.step_world_count(e, b)
        : {App.World.count(App.Sim.node(1n+e, App.WQuad{a, b, c, d}))
          == Nat.add(Nat.add(App.World.count(App.Sim.node(e, a)), _),
            Nat.add(App.World.count(c), App.World.count(d))) : Nat}
      %Laws.step_world_count(e, c)
        : {App.World.count(App.Sim.node(1n+e, App.WQuad{a, b, c, d}))
          == Nat.add(Nat.add(App.World.count(App.Sim.node(e, a)),
            App.World.count(App.Sim.node(e, b))), Nat.add(_, App.World.count(d))) : Nat}
      %Laws.step_world_count(e, d)
        : {App.World.count(App.Sim.node(1n+e, App.WQuad{a, b, c, d}))
          == Nat.add(Nat.add(App.World.count(App.Sim.node(e, a)),
            App.World.count(App.Sim.node(e, b))),
            Nat.add(App.World.count(App.Sim.node(e, c)), _)) : Nat}
      {==}
    case 1n+e App.WLeaf{ps}:
      Laws.step_parts_count(ps)
    case 0n App.WQuad{a, b, c, d}:
      {==}
