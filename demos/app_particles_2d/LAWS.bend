# Particles -- the simulation keeps every particle.  The list law is the
# leaf case; the world law covers the parallel quadtree step.
import Base
import ./main.bend as App

law step_parts_count:
  for +ps: App.Parts
  {App.Parts.count(App.Parts.step(ps)) == App.Parts.count(ps) : Nat}

law step_world_count:
  for +depth: Nat
  for +world: App.World
  {App.World.count(App.Sim.node(depth, world)) == App.World.count(world) : Nat}
