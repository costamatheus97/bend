# Sim + raster, two turns per frame

This experiment measures a particle simulation bang followed by host sprite
projection/binning and a Bend3D raster bang. It reuses
`../app_slash_boss_3d/bend3d.bend`; no renderer is copied. The simulation uses
independent particles attracted to scalar leaf-local centers. It is nbody-shaped,
not an all-pairs nbody solver.

Build and run from the worktree with its compiler:

```sh
export CC=/opt/rocm/llvm/bin/clang
bun bend2/main.ts demos/app_sim_raster_2d/main.bend -o /tmp/sim_raster
PARTICLES_SCALE=65536 /tmp/sim_raster --gpu 3GB
PARTICLES_PROBE=129 PARTICLES_SCALE=65536 /tmp/sim_raster --threads 16 --gpu off
```

`PARTICLES_SCALE` selects the small, medium (default), or large profile using
16384, 65536, or 262144. These are the particle totals at the default template
configuration; the probe reports the derived count after tuning.
`PARTICLES_PROBE=N` executes N total scripted frames without a window, discards
frames 0–7 from timings, and prints stage samples, medians and final checksums.
Use more than eight frames. The default runner uses 129 total frames, giving
121 measured samples. With an even sample count, the probe selects the upper
middle value. Without the probe variable, the 1024×768 window runs
until Esc or Close. The template configuration defs in `main.bend` control the
simulation depth and particles per leaf. Leaf grid spacing is fixed, so changing
depth also changes spatial extent; the recorded scale sweep keeps depth 7.

`Clock.us` is a small native effect backed by the runtime's monotonic clock.
`IO.now()` boundaries separate simulation from host binning and host forks
from rasterization. Bangs live in pure defs. The raster borrows the cell tree
and drops the old image down its existing tile fork; the host drops old cells
as part of the next build. No `App.run` or separate image-drop bang is used.
The raster has the reference depth-5 cell / depth-2 tile structure, with
16-pixel tiles and flat 4×4 loops; the reference prunes off-screen regions.

Run the full scale sweep with:

```sh
PARTICLES_OUT=/tmp/sim_raster_measurements sh demos/app_sim_raster_2d/run.sh
# CPU-only measurements if no GPU is available:
CPU_ONLY=1 PARTICLES_OUT=/tmp/sim_raster_cpu sh demos/app_sim_raster_2d/run.sh
```

The scripts build, check proofs, audit generated ownership operations and run
three rounds at every scale. `audit.sh` follows direct generated calls from the
bang roots and rejects counted operations; runtime helper internals are excluded. GPU/CPU
order alternates by round. Timing runs have GPU statistics disabled; a separate
stats run requires exactly `2*N` HIP turns, including warmups, and records device
and copy times by region. Missing GPU stats cannot produce an accepted GPU
summary. The runner checks that derived particle counts and final pixel/state checksums
agree across runs and lanes. The pixel hash is position-sensitive and invariant
under `Pix` compression; it covers the full 2048-square renderer image. The
state hash includes every F32 bit pattern. A checksum agreement is not a byte-for-byte equivalence proof.
Raw stdout, stderr, commands, exit status and JSON summaries go outside demos.
Set `PARTICLES_FRAMES` to change the total frame count. Dependencies are Bun,
Python 3, Clang and native window libraries; HIP builds also need ROCm. Set `CC`
if your compiler is elsewhere, and use your platform's ROCm library settings.

The reported FPS equivalent is `1e6 / median(total_us)`. It excludes window
presentation, pacing, startup, final checksumming and reporting. Stage medians
need not sum to the median total. GPU statistics are whole-run means including
warmups and final host reads, so they are not directly additive with warmed
stage medians.

A fused variant is not implemented for this pipeline. Current-frame host
projection/binning must occur between simulation and rasterization. A single
bang cannot span that host IO boundary. Moving the build and scene ownership
to the device would abandon the guide's ownership and host-build constraints;
rendering the previous world would change the dependency being measured.
This is a limitation of the chosen pipeline, not a claim that all fused particle
renderers are impossible.

See `RESULTS.md` for measurements, generated-code ownership checks and remaining
validation limits.
