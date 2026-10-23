#!/usr/bin/env python3
"""One-task replay of structural transfer lemmas with clean-import rebuild and mutation.
Output certifies Lean declarations only, never the unformalized global reduction.
"""
import hashlib,json,os,re,subprocess,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parent
AUDIT=HERE/'lean-audit'; AUDIT.mkdir(exist_ok=True)
IMPS=AUDIT/'imports'; IMPS.mkdir(exist_ok=True)

def run(name,args,env=None):
    start=time.perf_counter()
    r=subprocess.run(args,cwd=ROOT,env=env,text=True,capture_output=True)
    (AUDIT/(name+'.log')).write_text(r.stdout+r.stderr)
    return {'returncode':r.returncode,'seconds':time.perf_counter()-start,'log':str((AUDIT/(name+'.log')).relative_to(ROOT))},r.stdout+r.stderr

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

lean=str(ROOT/'bootloops-lean'); src=HERE/'Transfer.lean'; shared=ROOT/'research/rmaf/lean/RMAF.lean'
assert not re.search(r'\b(sorry|native_decide)\b|^\s*axiom\s',src.read_text(),re.M)
version,v=run('version',[lean,'--version']); assert version['returncode']==0
base,bl=run('shared-rebuild',[lean,'-o',str(IMPS/'RMAF.olean'),str(shared)]);assert base['returncode']==0
if 'sorryAx' in bl:raise AssertionError('shared import has sorryAx')
env=os.environ.copy();env['LEAN_PATH']=str(IMPS)
build,out=run('build',[lean,'-o',str(AUDIT/'Transfer.olean'),str(src)],env);assert build['returncode']==0
rows=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",out)
assert len(rows)==11,(len(rows),out)
allowed={'propext','Classical.choice','Quot.sound'}
for name,axioms in rows:
    assert set(x.strip() for x in axioms.split(',') if x.strip())<=allowed,(name,axioms)
# Change only the second graft order in the disagreement theorem. This makes
# its universal claim false; retain both source and actual compiler failure.
mut=src.read_text().replace('(augment rho (graft a b u)) s = false',
                           '(augment rho (graft b a u)) s = false',1)
assert mut!=src.read_text()
plant=AUDIT/'FalseSameOrder.lean';plant.write_text(mut)
neg,negative=run('negative-same-order',[lean,str(plant)],env)
assert neg['returncode']!=0 and 'unsolved goals' in negative
receipt={'scope':'11 kernel-checked declarations including actual restriction/span lemmas; whole AF map, unary-rho equivalence and thesis algorithm remain unformalized',
         'version':v.strip(),'version_run':version,'shared_import_rebuild':base,
         'build':build,'negative':neg,'axioms':dict(rows),
         'hashes':{str(p.relative_to(ROOT)):sha(p) for p in [src,shared,plant,Path(__file__)]}}
p=ROOT/'research/rmaf/results/thesis-transfer-lean.json';tmp=p.with_suffix('.json.tmp')
tmp.write_text(json.dumps(receipt,indent=2)+'\n');tmp.replace(p)
print(json.dumps({'declarations':len(rows),'negative_caught':True,'receipt':str(p.relative_to(ROOT))}))
