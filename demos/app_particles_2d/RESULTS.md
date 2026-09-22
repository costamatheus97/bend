# CPU validation; GPU measurement pending

2026-09-22, Ryzen 7 5800XT / WSL2, 16 CPU workers, ROCm Clang 22 `-O3`,
1024x768 output. Three runs per scale, each 8 warmups + 24 measured frames.
Every run explicitly used `--gpu off`. Values below are medians of the three
per-run upper medians, in microseconds; independent stage medians do not sum
to the total median. These are shared-host measurements, not GPU estimates.

| Particles | Sim | Host bin | Raster | Total | Pixel checksum | State checksum |
|---:|---:|---:|---:|---:|---:|---:|
| 16384 | 1190 | 5838 | 12654 | 20202 | 1887920887 | 2379102828 |
| 65536 | 1337 | 28367 | 48223 | 80366 | 2929207348 | 3183022968 |
| 262144 | 2262 | 167061 | 227372 | 404131 | 2044629747 | 4026567325 |

Checksums matched all three rounds at every scale. The state hash includes
all four F32 bit patterns per particle; the pixel hash includes image-tree
coordinates, sizes and colors (it is representation-sensitive, not a hash of
an expanded framebuffer). Both are U32 checksums. A separate 16K probe with
1 versus 2 measured frames changed both hashes, checking that state and image
advance. The probe total excludes presentation/pacing and checksum/reporting.

The full CPU_ONLY build runner also passed with 1 measured frame at every
scale, three rounds each. Its emitted C was byte-identical to the measured
binary's input. Generic particle-count laws check for flat leaves and all
quadtree/depth cases. They do not prove floating-point physics or rasterization.

Ownership scan of generated segments and transitively called native loops:
Sim.node reaches 13 definitions; raster Frame.node reaches 58. Both have
**0 term_keep, 0 ctr_take, 0 rfc_seal**. Raster has 5 term_peek sites. The sim
leaf is `spin_56` -> `spin_53`, a native tail loop reusing the consumed cons
storage; no per-particle continuation. The imported rasterizer is unchanged.

Commands run from the worktree (paths abbreviated only through these vars):

```sh
D=demos/app_particles_2d
P=/home/costamatheus97/vt/brainstorm-ai/bend2-hip/perf/sim-raster
bun bend2/main.ts "$D/PROOF.bend" --check-only
bun bend2/main.ts "$D/main.bend" -o "$P/logs/implementation/app-particles.c"
/opt/rocm/llvm/bin/clang -std=c11 -O3 "$P/logs/implementation/app-particles.c" -lpthread -lm -lX11 -o "$P/logs/implementation/app-particles-cpu"
sh "$D/measure.sh" "$P/logs/implementation/app-particles-cpu" "$P/logs/cpu-measurement" 24 cpu
CPU_ONLY=1 PARTICLES_FRAMES=1 PARTICLES_OUT="$P/logs/cpu-runner-check" bash "$P/run-gpu.sh"
python3 "$P/inspect-ownership.py" "$P/logs/implementation/app-particles.c" FID_SIM_NODE FID____APP_SLASH_BOSS_3D_BEND3D_FRAME_NODE_0
python3 "$P/test-runner.py"
shellcheck "$D/run_gpu.sh" "$D/measure.sh" "$P/run-gpu.sh"
bash "$P/validate-candidate.sh"
```

Raw timings: `logs/cpu-measurement/`, summary: `logs/cpu-measurement-summary.txt`.
Build/proof runner logs: `logs/cpu-runner-check/`. Ownership: `logs/implementation/ownership.txt`.
Synthetic runner tests reject wrong turns, checksum mismatches, process failures,
wrong/duplicate reports, missing stats and missing/duplicate copy regions.

No GPU device is exposed to this sandbox. GPU compilation/execution, actual
turn counts, device/copy timings, and CPU/GPU checksum equality are unverified.
Window mode compiles; no visual inspection was performed. The host command is
`bash "$P/run-gpu.sh"`; it requires successful GPU runs and exactly 2 turns per
executed frame, including warmups. Fused is omitted for the host dependency
explained in README.md. Confidence is high in CPU behavior; GPU performance
and exact F32 agreement remain open until that host run succeeds.

Git metadata is read-only in this sandbox, so no commit SHA was created.
The repo gate and diff check use a disposable candidate index/object directory
under /tmp, including all eight demo files. The host can run `bash "$P/commit.sh"`
to stage only this demo, recheck the gate, and commit on hip-sim-raster (no push).
