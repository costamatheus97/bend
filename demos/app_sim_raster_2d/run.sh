#!/bin/sh
# Native branch compiler; no installation or changes to the runtime.
# CPU_ONLY=1 selects only CPU measurements. OUT must be outside demos/.
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
out=${PARTICLES_OUT:-"$root/../../perf/sim-raster/sim_raster_$(date -u +%Y%m%dT%H%M%S)"}
mkdir -p "$out"
out=$(CDPATH= cd -- "$out" && pwd)
export CC=${CC:-/opt/rocm/llvm/bin/clang}
export BEND_NO_TELEMETRY=1
mode=both
if [ "${CPU_ONLY:-0}" = 1 ]; then mode=cpu; fi
cd "$root"
{ git rev-parse HEAD; git status --short; uname -a; "$CC" --version; } > "$out/environment.txt"
bun bend2/main.ts demos/app_sim_raster_2d/PROOF.bend --check-only > "$out/proof.log" 2>&1
bun bend2/main.ts demos/app_sim_raster_2d/main.bend -o "$out/particles.c" > "$out/emit.log" 2>&1
sh demos/app_sim_raster_2d/audit.sh "$out/particles.c" > "$out/ownership.txt"
bun bend2/main.ts demos/app_sim_raster_2d/main.bend -o "$out/particles" > "$out/build.log" 2>&1
sh demos/app_sim_raster_2d/measure.sh "$out/particles" "$out" "${PARTICLES_FRAMES:-129}" "$mode" > "$out/summary.txt" 2>&1 || {
  cat "$out/summary.txt"
  exit 1
}
cat "$out/summary.txt"
