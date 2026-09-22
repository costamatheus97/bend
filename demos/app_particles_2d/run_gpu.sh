#!/bin/bash
# Build from this worktree. CPU_ONLY=1 exercises the runner without a GPU.
set -euo pipefail
trap 'echo "FAIL: runner line $LINENO (see $out)" >&2' ERR
root=$(cd "$(dirname "$0")/../.." && pwd)
out=${PARTICLES_OUT:-"$root/../../perf/sim-raster/logs/$(date -u +%Y%m%dT%H%M%S)-$$"}
mkdir -p "$out"
out=$(cd "$out" && pwd)
export CC=${CC:-/opt/rocm/llvm/bin/clang}
mode=both
if [[ ${CPU_ONLY:-0} == 1 ]]; then
  export ROCM_PATH=/nonexistent CUDA_HOME=/nonexistent
  mode=cpu
fi
cd "$root"
{ git rev-parse HEAD; git status --short; uname -a; "$CC" --version
  echo "HSA_ENABLE_DXG_DETECTION=${HSA_ENABLE_DXG_DETECTION:-unset} LD_LIBRARY_PATH=${LD_LIBRARY_PATH:-unset}"
  sha256sum demos/app_particles_2d/{main.bend,clock.c} bend2/{bend.ts,comp.ts,base.bend} demos/app_slash_boss_3d/bend3d.bend
} > "$out/environment.txt"
bun bend2/main.ts demos/app_particles_2d/PROOF.bend --check-only > "$out/proof.log" 2>&1
bun bend2/main.ts demos/app_particles_2d/main.bend -o "$out/particles.c" > "$out/emit.log" 2>&1
bun bend2/main.ts demos/app_particles_2d/main.bend -o "$out/particles" > "$out/build.log" 2>&1
sh demos/app_particles_2d/measure.sh "$out/particles" "$out" "${PARTICLES_FRAMES:-128}" "$mode" | tee "$out/summary.txt"
