#!/bin/sh
# Direct generated call graph of the two pure bangs (no device closures here).
# Runtime helper internals are excluded; inspect reported source lines on failure.
set -eu
python3 - "$@" <<'PY'
import re,sys,json
from pathlib import Path
p=Path(sys.argv[1]); text=p.read_text(); nodes={}
def body(start):
    pos=text.index('{',start); depth=1; end=pos+1
    while depth:
        depth += (text[end]=='{')-(text[end]=='}'); end+=1
    return text[pos:end]
for m in re.finditer(r'^\s*WL_CASE\((FID_[A-Z0-9_]+)\)\s*\n\s*\{',text,re.M):
    nodes[m[1]]=(text.count('\n',0,m.start())+1,body(m.start()))
for m in re.finditer(r'^(?:INLINE|FAR) Term (spin_\d+)\(',text,re.M):
    nodes[m[1]]=(text.count('\n',0,m.start())+1,body(m.start()))
fids={m[1]:int(m[2]) for m in re.finditer(r'^#define (FID_[A-Z0-9_]+) (\d+)$',text,re.M)}
flags=list(map(int,re.search(r'FID_FLAG_T\[\] = \{([^}]+)',text)[1].strip(' ,').split(',')))
roots=[name for name,i in fids.items() if i<len(flags) and flags[i]&1]
seen=set(); todo=roots[:]
while todo:
    name=todo.pop()
    if name in seen or name not in nodes: continue
    seen.add(name)
    todo += re.findall(r'\b(?:FID_[A-Z0-9_]+|spin_\d+)\b',nodes[name][1])
result=[]
for name in sorted(seen,key=lambda n:nodes[n][0]):
    line,code=nodes[name]
    counts={key:len(re.findall(r'\b'+key+r'\(',code)) for key in ('term_keep','ctr_take','rfc_seal','term_peek')}
    result.append(dict(symbol=name,line=line,**counts))
print('Bang roots:',', '.join(roots))
print('Direct generated-code operations reachable from bangs (runtime helper internals excluded):')
for row in result: print(json.dumps(row))
print('Totals:', {k:sum(r[k] for r in result) for k in ('term_keep','ctr_take','rfc_seal','term_peek')})

if any(r[k] for r in result for k in ('term_keep','ctr_take','rfc_seal')):
    raise SystemExit('Counted operation in bang-reachable code: review ownership before accepting timings')
PY
