#!/bin/sh
# Usage: sh measure.sh BIN OUT [total frames=129] [both|cpu]
set -eu
python3 - "$@" <<'PY'
import json, os, pathlib, re, statistics, subprocess, sys, time
if not 3 <= len(sys.argv) <= 5:
    raise SystemExit('usage: measure.sh BIN OUT [total frames=129] [both|cpu]')
binary, out = pathlib.Path(sys.argv[1]).resolve(), pathlib.Path(sys.argv[2]).resolve()
frames = int(sys.argv[3]) if len(sys.argv) > 3 else 129
mode = sys.argv[4] if len(sys.argv) > 4 else 'both'
if frames <= 8 or mode not in ('both', 'cpu'):
    raise SystemExit('total frames must exceed 8; mode must be both or cpu')
out.mkdir(parents=True, exist_ok=True)
rows = []
def run(scale, lane, tag, stats=False):
    stem = out / f'{scale}-{lane}-{tag}'
    env = dict(os.environ, PARTICLES_PROBE=str(frames), PARTICLES_SCALE=str(scale))
    env.pop('BEND_GPU_STATS', None)
    if stats: env['BEND_GPU_STATS'] = '1'
    cmd = [str(binary), '--threads', '16', '--gpu', 'off' if lane == 'cpu' else '3GB']
    print(f'{stem.name}: {" ".join(cmd)}', flush=True)
    started = time.monotonic()
    with stem.with_suffix('.out').open('w') as stdout, stem.with_suffix('.err').open('w') as stderr:
        try:
            code = subprocess.run(cmd, env=env, stdout=stdout, stderr=stderr, timeout=1800).returncode
        except subprocess.TimeoutExpired:
            code = 124
    row = dict(scale=scale, lane=lane, run=tag, frames=frames, warmup=8, exit=code,
               command=cmd, wall_s=time.monotonic()-started)
    text, err = stem.with_suffix('.out').read_text(), stem.with_suffix('.err').read_text()
    med = re.search(r'^median_us sim (\d+) bin (\d+) raster (\d+) total (\d+)$', text, re.M)
    check = re.search(r'^checksum pixels (\d+) state (\d+)$', text, re.M)
    errors = []
    if code: errors.append(f'process exit {code}')
    if not med or not check: errors.append('missing median/checksum')
    if text.count('median_us ') != 1 or text.count('checksum pixels ') != 1:
        errors.append('ambiguous median/checksum report')
    headers = re.findall(r'^frames (\d+) warmup 8 particles (\d+)$', text, re.M)
    if len(headers) != 1 or int(headers[0][0]) != frames or int(headers[0][1]) < 1:
        errors.append('wrong workload header')
    else:
        row['particles'] = int(headers[0][1])
    if not errors:
        row['us'] = dict(zip(('sim','bin','raster','total'), map(int, med.groups())))
        row['checksum'] = list(map(int, check.groups()))
    if stats:
        s = re.search(r'hip (\d+) turns, passes (\d+) us', err)
        if not s or int(s[1]) != 2*frames:
            errors.append('GPU stats missing or expected 2 turns/frame not observed')
        else:
            row['turns_per_frame'] = int(s[1])/frames
            row['device_ms_per_frame'] = int(s[2])/frames/1000
        regions = re.findall(r'hip\s+(header|rings|heap|banks)\s+up \d+ calls \d+ KB (\d+) us, down \d+ calls \d+ KB (\d+) us', err)
        if len(regions) != 4 or {r[0] for r in regions} != {'header','rings','heap','banks'}:
            errors.append('missing copy-region stats')
        else:
            row['copies_ms_per_frame'] = {r[0]:(int(r[1])+int(r[2]))/frames/1000 for r in regions}
    if errors: row['error'] = '; '.join(errors)
    rows.append(row)
    (out/'runs.json').write_text(json.dumps(rows, indent=2)+'\n')
    print('  ' + row.get('error', str(row.get('us', {}))), flush=True)
for scale in (16384,65536,262144):
    for n in range(1,4):
        order = ('gpu','cpu') if n % 2 else ('cpu','gpu')
        for lane in order:
            if mode == 'both' or lane == 'cpu': run(scale,lane,str(n))
    if mode == 'both': run(scale,'gpu','stats',True)
summary = []
for scale in (16384,65536,262144):
    good = [r for r in rows if r['scale']==scale and 'error' not in r]
    counts = {r['particles'] for r in good}
    if len(counts)>1: raise SystemExit(f'PARTICLE COUNT MISMATCH for profile {scale}; see runs.json')
    checks = {tuple(r['checksum']) for r in good}
    if len(checks)>1: raise SystemExit(f'CHECKSUM MISMATCH at {scale}; see runs.json')
    for lane in ('gpu','cpu'):
        group = [r for r in good if r['lane']==lane and r['run']!='stats']
        validated = lane == 'cpu' or any(r['run']=='stats' for r in good)
        if len(group)==3 and validated:
            ms = {s:statistics.median(r['us'][s] for r in group)/1000 for s in ('sim','bin','raster','total')}
            summary.append(dict(profile=scale,particles=group[0]['particles'],lane=lane,stage_ms=ms,fps=1000/ms['total'],checksum=group[0]['checksum']))
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
if any('error' in r for r in rows):
    raise SystemExit('Some requested measurements unavailable; see runs.json and raw logs')
PY
