#!/usr/bin/env python3
"""One-shot independent rebuild of delivered v2; explicit witnesses only."""
from pathlib import Path
import subprocess,json,hashlib,os,re,time
B=Path(__file__).resolve().parent;W=B.parents[4];R=B.parent/'edge_route/second_exchange_v2';L=B/'lean-v2';L.mkdir(exist_ok=True)
lean=W/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean';env=dict(os.environ);env['LEAN_PATH']=str(L)
rows=[]
for name in ['ParentTransport','YieldTransport','SecondCut','PositiveControls','NegativeControl']:
    source=R/(name+'.lean');data=source.read_bytes();dest=L/source.name;dest.write_bytes(data)
    clean=re.sub(r'/\-.*?\-/','',data.decode(),flags=re.S);clean=re.sub(r'--[^\n]*','',clean)
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',clean)
    t0=time.perf_counter();p=subprocess.run([str(lean),'-o',str(L/(name+'.olean')),str(dest)],cwd=L,env=env,text=True,capture_output=True,timeout=60)
    log=p.stdout+p.stderr;(L/(name+'.log')).write_text(log)
    assert (p.returncode!=0)==(name=='NegativeControl'),(name,log)
    if name!='NegativeControl':
      assert 'sorryAx' not in log
      for d in re.findall(r'depends on axioms:\s*\[([^]]*)\]',log): assert set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*',d))<={'propext','Classical.choice','Quot.sound'}
    rows.append({'module':name,'source_sha256':hashlib.sha256(data).hexdigest(),'returncode':p.returncode,'expected_rejection':name=='NegativeControl','elapsed_seconds':time.perf_counter()-t0,'unchanged':source.read_bytes()==dest.read_bytes()})
audit=L/'ExtraAxioms.lean';audit.write_text('import PositiveControls\n#print axioms TreeControls.lower_splice\n#print axioms TreeControls.upper_splice\n')
p=subprocess.run([str(lean),str(audit)],cwd=L,env=env,text=True,capture_output=True,timeout=60);assert p.returncode==0
(L/'ExtraAxioms.log').write_text(p.stdout+p.stderr)
d={'rows':rows,'extra_axioms':p.stdout.strip(),'scope':'two witnessed recursive pendant splices, conditional parent-map commutation and second-rule support; geometry-to-encoding and graph-yield correspondence remain prose/open formal interface'}
(B/'lean-v2.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d,indent=2))
