#!/bin/bash
# Stage 1 fault attribution on the HIP lane (a measurement build, not the
# runtime): emit the probe's C, splice attrib.c's phase tags and fault
# hooks and reach.c's reach_dev walker into it, build, and run it with
# BEND_GPU_STATS=1 at each scale. Usage: ATTRIB_OUT=<dir> bash demos/app_particles_2d/attrib.sh
# [frames=32] [scales="16384 65536 262144"; "" builds only]. BEND_GPU_WALK=0
# skips the walks; ATTRIB_TIMEOUT bounds a run (s, default 300).
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
out=${ATTRIB_OUT:?set ATTRIB_OUT}
mkdir -p "$out"
out=$(cd "$out" && pwd)
export CC=${CC:-/opt/rocm/llvm/bin/clang}
rocm=${ROCM_PATH:-/opt/rocm}
libs=()
cd "$root"
git rev-parse HEAD > "$out/head.txt"
bun bend2/main.ts demos/app_particles_2d/main.bend -o "$out/particles.c" > "$out/emit.log" 2>&1
python3 - "$out/particles.c" demos/app_particles_2d/{attrib,reach}.c <<'PY'
import re, sys
path, lib = sys.argv[1], open(sys.argv[2]).read() + open(sys.argv[3]).read()
part = dict(re.findall(r'^//@ (\w+)\n(.*?)(?=^//@ |\Z)', lib, re.S | re.M))
s = open(path).read()
def at(old, new):
    global s
    if s.count(old) != 1:
        sys.exit(f'attrib: {s.count(old)} matches for {old[:60]!r}')
    s = s.replace(old, new)
def before(anchor, text): at(anchor, text + anchor)
def after(anchor, text): at(anchor, anchor + text)
before('// Cls\n// ===\n', part['tags'] + '\n')
after('    out[y * w + x] = window_pix(H, root, k, x, y);\n  }\n}\n#endif\n',
  part['kernel'])
before('// Cli\n// ===\n', part['host'] + part['walk'] + '\n')
after('OUTLINE Loc heap_alloc_miss(Env e, Cls cls) {\n  Corpus H = e.mem;\n'
  '  Loc  got = 0;\n', '  AT_IN(1);\n  at_pop(e, cls, 0, false);\n')
after('    got = bank_pop(H, cls);\n', '    at_pop(e, cls, got, true);\n')
before('      return HEAP_OFF;\n', '      AT_OUT(1);\n')
at('  ALC_LEN(e, cls) = (u64)(n - 1) << cls;\n  return got;\n',
  '  ALC_LEN(e, cls) = (u64)(n - 1) << cls;\n  AT_OUT(1);\n  return got;\n')
at('    ALC_LEN(e, cls) -= 1ull << cls;\n    return h;\n  }\n'
  '  return heap_alloc_miss(e, cls);\n}',
  '    ALC_LEN(e, cls) -= 1ull << cls;\n  } else {\n'
  '    h = heap_alloc_miss(e, cls);\n  }\n  AT_OUT(2);\n  AT_NEW(h, cls);\n'
  '  return h;\n}')
after('INLINE Loc heap_alloc(Env e, Cls cls) {\n  Loc h = ALC_AT(e, cls);\n',
  '  AT_IN(2);\n  AT_LC(e, cls);\n')
at('  e.mem[loc]       = ALC_AT(e, cls);\n',
  '  AT_IN(3);\n  e.mem[loc]       = ALC_AT(e, cls);\n  AT_OUT(3);\n')
at('FAR void term_drop(Env e, Term t) {', 'FAR void term_drop_(Env e, Term t) {')
before('INLINE void term_sink(Env e, Term t) {', 'FAR void term_drop(Env e, '
  'Term t) {\n  AT_IN(4);\n  term_drop_(e, t);\n  AT_OUT(4);\n}\n\n')
at('OUTLINE void span_fade(Env e, Term t, Loc src, u32 n) {',
  'OUTLINE void span_fade_(Env e, Term t, Loc src, u32 n) {')
at('INLINE Loc ctr_take(Env e, Term t, u32 n, THR Term* out) {',
  'OUTLINE void span_fade(Env e, Term t, Loc src, u32 n) {\n  AT_IN(5);\n'
  '  span_fade_(e, t, src, n);\n  AT_OUT(5);\n}\n\n'
  'INLINE Loc ctr_take_(Env e, Term t, u32 n, THR Term* out) {')
before('INLINE Term term_word(Env e, Term w) {', 'INLINE Loc ctr_take(Env e, '
  'Term t, u32 n, THR Term* out) {\n  AT_IN(5);\n  Loc l = ctr_take_(e, t, n, '
  'out);\n  AT_OUT(5);\n  return l;\n}\n\n')
after('      __atomic_fetch_add(&gpu_writes, 1, __ATOMIC_RELAXED);\n',
  '      if (gpu_stat) {\n        at_fault(c, addr, 2);\n      }\n')
after('      u8  to = wr == 1 ? GPU_DIRTY : GPU_CLEAN;\n',
  '      if (gpu_stat) {\n        at_pre(c);\n      }\n')
at('        hipMemcpyDeviceToHost) == hipSuccess\n        && mprotect(',
  '        hipMemcpyDeviceToHost) == hipSuccess\n'
  '        && (!gpu_stat || at_fault(c, addr, wr == 1))\n        && mprotect(')
at('  gpu_part = 0;\n}\n\n#define gpu_enter() gpu_sync(true)',
  '  gpu_part = 0;\n  if (gpu_stat && up) {\n    at_enter();\n  }\n}\n\n'
  '#define gpu_enter() gpu_sync(true)')
at('        gpu_enter();\n        cube_run(H, true);\n        gpu_leave();\n',
  '        at_argn = fid_arity((u32)term_aux(t));\n'
  '        at_argn = at_argn < 8 ? at_argn : 8;\n'
  '        for (u32 j = 0; j < 8; j += 1) {\n'
  '          at_arg[j] = j < at_argn ? H[term_loc(t) + j] : 0;\n'
  '        }\n        gpu_enter();\n'
  '        cube_run(H, true);\n        gpu_leave();\n        at_leave();\n')
open(path, 'w').write(s)
PY
if grep -q '^#include <X11/' "$out/particles.c"; then
  libs=(-lX11)
fi
"$CC" -DBEND_HIP=1 -D__HIP_PLATFORM_AMD__ -I"$rocm/include" -L"$rocm/lib" \
  -Wl,-rpath,"$rocm/lib" -std=c11 -O3 "$out/particles.c" -lpthread -lm \
  "${libs[@]}" -o "$out/particles" -lamdhip64 -lhiprtc > "$out/build.log" 2>&1
timeout 300 "$out/particles" --gpu-build >> "$out/build.log" 2>&1
for scale in ${2-16384 65536 262144}; do
  BEND_GPU_STATS=1 PARTICLES_PROBE=${1:-32} PARTICLES_SCALE=$scale \
    timeout "${ATTRIB_TIMEOUT:-300}" "$out/particles" --threads 16 --gpu 3GB \
    > "$out/$scale.out" 2> "$out/$scale.err"
  echo "== $scale: $(grep -o 'median_us.*' "$out/$scale.out")"
  grep -h 'checksum\|hip [0-9]* turns\|heap  \|^attrib' "$out/$scale.out" "$out/$scale.err"
done
