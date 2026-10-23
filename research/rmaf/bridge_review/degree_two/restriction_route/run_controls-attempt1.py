# One-shot Lean control harness: no toolkit package supplies RMAF-specific semantics.
# It checks frozen hand-authored propositions, retains all failures, and never grants
# semantic credit for parser/elaborator diagnostics unrelated to explicit falsity.
from pathlib import Path
import subprocess,time,json,hashlib,datetime
ROOT=Path(__file__).resolve().parents[5]
D=Path(__file__).resolve().parent
BUILD=D/'build'
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'runs':[]}
def run(name,args,expected,semantic=False):
    start=time.monotonic(); p=subprocess.run(args,cwd=ROOT,text=True,capture_output=True,env=__import__('os').environ|{'LEAN_PATH':str(BUILD)})
    log=p.stdout+p.stderr; (D/(name+'.log')).write_text(log)
    ok=(p.returncode==0) if expected=='pass' else (p.returncode!=0)
    if semantic: ok=ok and 'evaluated to `false`' in log
    receipt['runs'].append({'name':name,'seconds':time.monotonic()-start,'returncode':p.returncode,'expected':expected,'semantic_false':semantic,'accepted':ok})
    (D/'controls-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    assert ok,(name,log)
lean=str(ROOT/'bootloops-lean')
run('pilot-rmaf',[lean,'-o',str(BUILD/'RMAF.olean'),str(ROOT/'research/rmaf/lean/RMAF.lean')],'pass')
run('controls-positive',[lean,'-o',str(BUILD/'Controls.olean'),str(D/'Controls.lean')],'pass')
false=[('cross-address','minimalVertices [0] tRoot = minimalVertices [0] uRoot'),('wrong-degree','degree (minimalVertices [0,1] tRoot) [] = 3'),('missing-path','minimalVertices [0,2] tPath = [[],[false,false],[true]]'),('wrong-root','[] ∈ minimalVertices [0] tPath'),('overlap','disjointVertices (minimalVertices [0,2] tFour) (minimalVertices [1,3] tFour) = true'),('wrong-cost','([[0],[2],[1],[3]] : List (List Nat)).length = ([[0,2],[1],[3]] : List (List Nat)).length'),('repeated-labels','(leaves (.node (.leaf 0) (.leaf 0))).Nodup')]
for name,prop in false:
    f=D/(name+'.lean'); f.write_text('import Controls\nopen RMAF RestrictionRouteControls\nexample : '+prop+' := by decide\n')
    run(name,[lean,str(f)],'fail',True)
f=D/'malformed.lean'; f.write_text('import Controls\n#check deliberately_missing_identifier\n')
run('malformed',[lean,str(f)],'fail')
receipt['hashes']={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in [ROOT/'research/rmaf/lean/RMAF.lean',D/'CONTROL-PIN.md',D/'Controls.lean',Path(__file__)]}
receipt['status']='positive controls passed; seven explicit false propositions rejected; malformed control diagnostic only'
(D/'controls-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(receipt['status'])
