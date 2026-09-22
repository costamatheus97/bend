#!/bin/sh
# Usage: sh measure.sh BIN OUT [measured frames=128] [both|cpu]
set -eu
python3 - "$@" <<'PY'
import json, os, pathlib, re, statistics, subprocess, sys
binary, out = pathlib.Path(sys.argv[1]).resolve(), pathlib.Path(sys.argv[2]).resolve()
frames = int(sys.argv[3]) if len(sys.argv) > 3 else 128
mode = sys.argv[4] if len(sys.argv) > 4 else 'both'
if frames < 1 or mode not in ('both', 'cpu'):
    raise SystemExit('frames must be positive; mode must be both or cpu')
out.mkdir(parents=True, exist_ok=True)
rows, checks = [], {}
def run(scale, lane, tag, stats=False):
    stem = out / f'{scale}-{lane}-{tag}'
    env = dict(os.environ, PARTICLES_PROBE=str(frames), PARTICLES_SCALE=str(scale))
    env.pop('BEND_GPU_STATS', None)
    if stats:
        env['BEND_GPU_STATS'] = '1'
    cmd = [str(binary), '--threads', '16', '--gpu', 'off' if lane == 'cpu' else '3GB']
    print(f'{stem.name}: {" ".join(cmd)}', flush=True)
    with stem.with_suffix('.out').open('w') as stdout, stem.with_suffix('.err').open('w') as stderr:
        p = subprocess.run(cmd, env=env, stdout=stdout, stderr=stderr, timeout=1800)
    def require(ok, why):
        if not ok:
            raise SystemExit(f'FAIL {stem}: {why}; inspect .out/.err')
    require(p.returncode == 0, f'exit {p.returncode}')
    text, err = stem.with_suffix('.out').read_text(), stem.with_suffix('.err').read_text()
    headers = re.findall(r'^particles=.*$', text, re.M)
    require(headers == [f'particles={scale} frames={frames} warmup=8'], 'wrong workload')
    require(text.count('median_us ') == text.count('checksum pixels ') == 1, 'ambiguous report')
    med = re.search(r'median_us sim (\d+) bin (\d+) raster (\d+) total (\d+)', text)
    check = re.search(r'checksum pixels (\d+) state (\d+)', text)
    require(med and check, 'missing medians/checksum')
    check = tuple(map(int, check.groups()))
    require(check == checks.setdefault(scale, check), 'CHECKSUM MISMATCH')
    row = dict(scale=scale, lane=lane, run=tag, us=list(map(int, med.groups())), checksum=check)
    if stats:
        s = re.search(r'hip (\d+) turns, passes (\d+) us', err)
        require(s and int(s[1]) == 2*(frames+8), 'expected 2 GPU turns/frame including warmups')
        row['turns_per_frame'] = int(s[1])/(frames+8)
        row['device_ms_per_frame'] = int(s[2])/(frames+8)/1000
        regions = re.findall(r'hip\s+(header|rings|heap|banks)\s+up (\d+) calls (\d+) KB (\d+) us, down (\d+) calls (\d+) KB (\d+) us', err)
        require(len(regions) == 4 and {r[0] for r in regions} == {'header','rings','heap','banks'}, 'invalid copy regions')
        row['copies'] = {r[0]:dict(zip(('up_calls','up_KB','up_us','down_calls','down_KB','down_us'),map(int,r[1:]))) for r in regions}
        print(f"  turns/frame=2 device_ms/frame={row['device_ms_per_frame']:.3f}")
        print('  copies (whole run): ' + json.dumps(row['copies']))
    rows.append(row)
    (out/'runs.json').write_text(json.dumps(rows, indent=2)+'\n')
for scale in (16384,65536,262144):
    for n in range(1,4):
        for lane in (('gpu','cpu') if mode == 'both' else ('cpu',)):
            run(scale,lane,str(n))
    if mode == 'both':
        run(scale,'gpu','stats',True)
print('particles lane sim_us bin_us raster_us total_us pixels state')
for scale in checks:
    for lane in ('gpu','cpu'):
        group = [r for r in rows if r['scale']==scale and r['lane']==lane and r['run']!='stats']
        if group:
            med = [statistics.median(r['us'][i] for r in group) for i in range(4)]
            print(scale,lane,*med,*checks[scale])
PY
