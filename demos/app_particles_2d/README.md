# Simulation + raster measurement

This demo measures dependent GPU turns per frame: update a quadtree of
particle lists, bin its sprites into 64-px cells, then rasterize them using
the sibling Bend3D renderer. It intentionally tests SHADERS.md's warning about
two bangs/frame.
The fixed scalar attractors make it nbody-shaped, not an all-pairs nbody model.

On this machine the HIP lane only finds the card with:

```sh
export HSA_ENABLE_DXG_DETECTION=1
export LD_LIBRARY_PATH=/home/costamatheus97/vt/brainstorm-ai/hip-probe/rocdxg/lib
```

Build from the worktree:

```sh
CC=/opt/rocm/llvm/bin/clang bun bend2/main.ts demos/app_particles_2d/main.bend -o /tmp/particles
```

Run `/tmp/particles --gpu 3GB` for the window; Esc closes it.
`PARTICLES_SCALE` selects 1024, 4096, 16384, 65536 (default), 262144 or
1048576 particles. `PARTICLES_PROBE=N` runs N measured frames after eight
warmup frames, without opening a window.
`--gpu off` explicitly selects the CPU pool.

`PARTICLES_BIN` selects where the binning runs; any other value is `host`:

- `host` (default): sim bang, host binning, raster bang. On the HIP lane the
  host's walk of the world faults the sim bang's writes back.
- `device`: sim bang, then one bang that bins and rasterizes; last frame's
  cells are freed inside it, so the host never walks the world or the cells.
- `fused`: one bang a frame for sim, binning and raster.

All three draw the same pixels and states (the same `Scene.build`). The probe
prints `bin=<mode>` on its own line; its sim/bin/raster columns are the clock gaps around each
step, so `device` reports its binning under raster (bin ~0) and `fused` its
whole frame under raster. Binning forks its merges over the cell quadtree in
worlds of 65,536 and up (`Pm.m2`): a merge on one lane walked every list at
the root.

Run `bash demos/app_particles_2d/run_gpu.sh` on the GPU host. It rebuilds,
checks proofs and runs three interleaved GPU/CPU rounds at each scale, then a
separate instrumented GPU run. Raw logs and the summary live under
`perf/sim-raster/logs/` beside the worktrees. Override `PARTICLES_OUT` for an
explicit destination or `PARTICLES_FRAMES` (default 128) for measured frames.
`CPU_ONLY=1` builds without HIP and tests the CPU paths. Requires Bun, Python 3,
Clang (defaults to ROCm's), and native window development libraries. GPU builds
also require the HIP runtime and host GPU access.

The runner fails on compilation, workload, checksum or turn-count errors.
Timing rows are medians of three per-run stage upper medians, in microseconds; the
separate stats run reports device milliseconds/frame and copies by region.
Stats include warmups and final checksum/teardown traffic; measured stage
medians exclude warmups. A headless total is compute throughput, not displayed
FPS: it excludes window presentation and pacing.

`device` and `fused` go against the guide's host-scene advice on purpose:
they measure what device binning costs against the host's faults. Pipelining
rasterization of a previous frame would measure a different dependency.

CPU measurements, validation commands, emitted-C ownership findings and GPU
limitations are recorded in RESULTS.md. GPU performance remains unmeasured
until the host runs the script; CPU numbers are not GPU estimates.
