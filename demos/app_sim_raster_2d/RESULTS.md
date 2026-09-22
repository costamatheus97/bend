# Sim + raster results — 2026-09-22

The CPU baseline is measured. The requested RX 7800 XT comparison is **blocked**:
this session exposes no `/dev/dxg`, `/dev/kfd`, or render device. Every native
`--gpu 3GB` attempt exited 1 with `bend: --gpu on, but this binary found no GPU device`.
No GPU run, speedup, real-time GPU claim, transfer timing or GPU/CPU checksum
identity is inferred from CPU results or offline compilation.

Base: `0d91fcb67627e7854ab356fa6d124d57813f6664`, worktree `pr/sim-raster`, branch
`hip-sim-raster`. CPU: Ryzen 7 5800XT, 8 cores/16 logical CPUs, WSL2; CPU pool
explicitly 16 threads. Compiler: branch `bun bend2/main.ts`, ROCm Clang at
`/opt/rocm/llvm/bin/clang`. Raw logs, emitted C, native executable, source/binary
SHA256, screenshot and JSON results are under:
`/home/costamatheus97/vt/brainstorm-ai/bend2-hip/perf/sim-raster/isolated-demo/`.

## Timing

Three rounds per scale, 129 total frames each, first 8 excluded (121 samples).
Order: GPU/CPU, CPU/GPU, GPU/CPU; GPU attempts failed before executing a frame.
A separate instrumented GPU attempt per scale also failed. CPU timing runs had
`BEND_GPU_STATS` unset. Values below are medians of the three per-run medians.
FPS equivalent is 1000/total_ms, excluding presentation, pacing, startup,
reporting and final checksum. Stage medians need not sum to median total.

| Particles | Lane | Sim ms | Host bin ms | Raster ms | Total ms | FPS equivalent |
|---:|---|---:|---:|---:|---:|---:|
| 16,384 | CPU pool | 1.161 | 3.714 | 18.049 | 22.866 | 43.73 |
| 65,536 | CPU pool | 1.415 | 19.639 | 68.515 | 90.275 | 11.08 |
| 262,144 | CPU pool | 2.224 | 122.786 | 329.636 | 455.596 | 2.19 |

| GPU workload | Turns/frame measured | Device ms/frame | Copies ms/frame: header / rings / heap / banks | GPU/CPU speedup |
|---|---|---|---|---|
| Two-bang, all three scales | unavailable | unavailable | unavailable / unavailable / unavailable / unavailable | unavailable |
| Fused | not implemented | — | — | — |

The emitted program has exactly two bang roots, simulation and raster, but
actual GPU turns/frame remains unverified. `measure.sh` refuses GPU summaries
without a successful stats run proving `2*N` turns. `--gpu-build` can return
success when no device exists; native build success does not prove execution.

All nine CPU runs (microseconds, including the observed variation):

| Particles | Run | Sim | Bin | Raster | Total |
|---:|---:|---:|---:|---:|---:|
| 16,384 | 1 | 1161 | 3714 | 18049 | 22866 |
| 16,384 | 2 | 1166 | 3723 | 18038 | 22773 |
| 16,384 | 3 | 1159 | 3670 | 18241 | 23063 |
| 65,536 | 1 | 1423 | 20529 | 68515 | 91058 |
| 65,536 | 2 | 1412 | 19639 | 68812 | 90275 |
| 65,536 | 3 | 1415 | 18782 | 67938 | 88714 |
| 262,144 | 1 | 2224 | 122786 | 329636 | 455596 |
| 262,144 | 2 | 2361 | 133278 | 376446 | 511212 |
| 262,144 | 3 | 2173 | 115154 | 314150 | 436241 |

Raster and host binning dominate this workload as density increases. At 256K,
the per-run total medians range from 436.241 to 511.212 ms; these are noisy local
measurements, not a pinned performance claim. No GPU win/loss crossover can be
identified without the missing GPU measurements.

## Checksums and verification

All three CPU runs agree at each scale:

| Particles | Pixel hash | State hash (F32 bits) |
|---:|---:|---:|
| 16,384 | 3564427229 | 3806264534 |
| 65,536 | 1543298353 | 5320405 |
| 262,144 | 345827093 | 622795228 |

The 16K one-thread replay also matches the 16-thread hashes after 129 frames.
GPU/CPU identity is **not tested**. Pixel hashing is quadrant-order-sensitive
and normalizes compressed `Pix` squares; it covers the full 2048-square image.
A 32-bit checksum agreement is not a byte-for-byte equivalence proof.

Main and PROOF typecheck; native build passes. The staged repository gate passes
`PASS: 46 / 46`, and `git diff --cached --check` passes. Offline HIPRTC compilation for
`gfx1101` passes with the runtime's flags (`-DCUBE_LOG=7 -O3 -ffp-contract=off`),
producing 114,272 bytes of device code. This validates compilation only.
The 1024x768 CPU window was captured and inspected; sprites fill the frame,
and a sent Escape event closes it with exit 0 (`window.png`, `window-check.txt`).

`timing-validation.txt` independently verifies all nine runs: sample indices
are exactly 8..128; each total equals its three stage durations; all reported
medians match Python's median over the 121 samples. Regression checks show the
old additive pixel checksum fails the new pixel-position law; compression
invariance passes. Changing depth to 6 in an isolated copy preserves proofs and
reports 4096 particles for the small profile. Synthetic runner tests reject
wrong turns, mismatched checksums/counts, duplicate reports, wrong frame counts,
missing output and process failures; tuned reported counts are recorded correctly.

Generated C ownership audit (`ownership.txt`, `ownership-grep.txt`):

| Device-reachable code | Emitted C location | term_keep | ctr_take | rfc_seal |
|---|---|---:|---:|---:|
| Flat simulation list loop | spin_55, particles.c:5393 | 0 | 0 | 0 |
| Raster 4x4 block list loop | spin_24, particles.c:3342 | 0 | 0 | 0 |
| Tile.go, including old-image sinks | spin_43, particles.c:4913 | 0 | 0 | 0 |
| All generated defs reachable from both bang roots | audit.sh direct call graph | 0 | 0 | 0 |

The raster block loop uses `term_peek`; the sim loop consumes/reuses its own list.
Runtime helper internals and host reporting defs are outside this audit's scope.
An injected keep in the sim def makes the audit fail, validating the check.

## Implementation and limits

`main.bend:136` is the flat sim list loop; `main.bend:161` is its pure bang.
`main.bend:217` builds cell lists and drops the previous scene on the host;
`main.bend:236` delegates the pure borrowed-cell raster bang to Bend3D.
`main.bend:363` places IO boundaries around the stages. The existing renderer
keeps depth 5 to 64-pixel cells and depth 2 to 16-pixel tiles; off-screen pruning
means 3072 visible tiles at 1024x768, rather than all 16384 possible tiles busy.
The window displays the root's top-left 1024-square quadrant and reconstructs
the full old root before the next raster (`main.bend:416`).

No fused variant: the chosen pipeline requires current-frame host binning
between sim and raster. A single bang cannot include that host IO step; moving
scene construction/ownership onto the device abandons the guide constraints.
A differently partitioned fused renderer may be possible, but would not be
this pipeline. The force model uses one fixed scalar center per leaf and no
shared all-pairs particle list. Confidence is high in the CPU checks and static
ownership findings; runtime GPU scheduling, floating-point/checksum identity,
GPU performance and transfer costs remain unvalidated.

## Commands

Run from the requested worktree. `OUT` below abbreviates the raw directory above;
these are the commands executed, with the recorded script expanding all runs.
The HIP environment matches `perf/turn/env.sh`.

```sh
export CC=/opt/rocm/llvm/bin/clang BEND_NO_TELEMETRY=1
OUT=/home/costamatheus97/vt/brainstorm-ai/bend2-hip/perf/sim-raster/isolated-demo
bun bend2/main.ts demos/app_sim_raster_2d/PROOF.bend --check-only
bun bend2/main.ts demos/app_sim_raster_2d/main.bend -o "$OUT/particles.c"
sh demos/app_sim_raster_2d/audit.sh "$OUT/particles.c"
bun bend2/main.ts demos/app_sim_raster_2d/main.bend -o "$OUT/particles"
HSA_ENABLE_DXG_DETECTION=1 LD_LIBRARY_PATH=/home/costamatheus97/vt/brainstorm-ai/hip-probe/rocdxg/lib sh demos/app_sim_raster_2d/measure.sh "$OUT/particles" "$OUT" 129 both
PARTICLES_PROBE=129 PARTICLES_SCALE=16384 "$OUT/particles" --threads 1 --gpu off
python3 /tmp/sim-raster-window-check.py
/home/costamatheus97/vt/brainstorm-ai/bend2-hip/perf/sim-raster/compile_hip "$OUT/particles.c"
bun gates/repo.ts
git diff --cached --check
```

The matrix exits 1 intentionally because its GPU requests failed; all nine CPU
subprocesses exit 0. Individual commands/statuses are in `runs.json`; stage
samples are `*-cpu-*.out`, GPU failures are `*-gpu-*.err`. The offline HIPRTC
helper source is `perf/sim-raster/compile_hip.c`; it uses the same four compiler
options as the runtime. `run.sh` provides a single reproducible build/audit/run
entry point for a session with device access (`CPU_ONLY=1` for the CPU baseline).
