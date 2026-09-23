# Simulation + raster measurement

This demo measures two dependent GPU turns per frame: update a quadtree of
particle lists, then rasterize host-binned sprites using the sibling Bend3D
renderer. It intentionally tests SHADERS.md's warning about two bangs/frame.
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

A fused variant is omitted: current-frame host binning must run after the sim
returns and before the raster starts. One device call cannot span that host IO
boundary. Moving projection/binning onto the device changes the prescribed
pipeline and violates the guide's host-scene construction advice. Pipelining
rasterization of a previous frame would measure a different dependency.

CPU measurements, validation commands, emitted-C ownership findings and GPU
limitations are recorded in RESULTS.md. GPU performance remains unmeasured
until the host runs the script; CPU numbers are not GPU estimates.
