# One-shot source-bound Lean replay of this independently authored route.
# Toolkit consultation: no indexed package supplies RMAF proof compilation or
# this exact transport audit; the existing bootloops-lean wrapper is used as-is.
from pathlib import Path
import subprocess,time,json,hashlib,datetime,os,re
ROOT=Path(__file__).resolve().parents[5]
D=Path(__file__).resolve().parent
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
OUT=D/'replay'/stamp
OUT.mkdir(parents=True,exist_ok=False)
BUILD=OUT/'build';BUILD.mkdir()
record={'utc':stamp,'status':'running','grade':'author replay; fresh review pending','runs':[],'sources':{}}
modules=[ROOT/'research/rmaf/lean/RMAF.lean']+[D/(n+'.lean') for n in ['RestrictionTransport','SupportAlgebra','SupportProfile','ActualSupportTransport','Controls','TransportUseSites']]
for src in modules+[D/'ROUTE-PIN-v1.md',D/'ROUTE-AMENDMENT-v2.md',D/'CONTROL-PIN.md',Path(__file__)]:
    record['sources'][str(src.relative_to(ROOT))]=hashlib.sha256(src.read_bytes()).hexdigest()
def run(name,args,expected,semantic=False):
    start=time.monotonic()
    p=subprocess.run(args,cwd=ROOT,text=True,capture_output=True,env=os.environ|{'LEAN_PATH':str(BUILD)})
    log=p.stdout+p.stderr;(OUT/(name+'.log')).write_text(log)
    ok=p.returncode==0 if expected=='pass' else p.returncode!=0
    if expected=='pass': ok=ok and 'sorryAx' not in log and 'error:' not in log
    if semantic: ok=ok and 'Tactic `decide` proved that the proposition' in log and 'is false' in log
    record['runs'].append({'name':name,'seconds':time.monotonic()-start,'exit':p.returncode,'expected':expected,'semantic_false':semantic,'accepted':ok,'log_sha256':hashlib.sha256(log.encode()).hexdigest()})
    (OUT/'receipt.json').write_text(json.dumps(record,indent=2)+'\n')
    assert ok,(name,log)
    return log
lean=str(ROOT/'bootloops-lean')
for src in modules:
    run(src.stem,[lean,'-o',str(BUILD/(src.stem+'.olean')),str(src)],'pass')
for name in ['cross-address','wrong-degree','missing-path','wrong-root','overlap','wrong-cost','repeated-labels']:
    run('false-'+name,[lean,str(D/(name+'.lean'))],'fail',True)
run('diagnostic-malformed',[lean,str(D/'malformed.lean')],'fail')
for src in modules:
    text=src.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',re.sub(r'/\-.*?\-/','',text,flags=re.S)),src
record['status']='all requested author checks passed'
record['scope']='universal restriction and cross-tree support transport; original partition refinement remains parent scope'
record['independence']='shared actual RMAF definition and Lean kernel; no graph route or parent LocalSplit read; final nonauthor review not performed by this script'
(OUT/'receipt.json').write_text(json.dumps(record,indent=2)+'\n')
(D/'FINAL-REPLAY.json').write_text(json.dumps({'receipt':str((OUT/'receipt.json').relative_to(ROOT)),'sha256':hashlib.sha256((OUT/'receipt.json').read_bytes()).hexdigest(),'status':record['status'],'grade':record['grade']},indent=2)+'\n')
print(json.dumps({'receipt':str(OUT/'receipt.json'),'status':record['status']}))
