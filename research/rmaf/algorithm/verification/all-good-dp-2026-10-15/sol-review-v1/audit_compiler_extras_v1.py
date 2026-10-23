"""One-shot compiler-only name metadata audit, distinct from ConstantInfo bodies."""
from pathlib import Path
from hashlib import sha256
from datetime import datetime,timezone
import json,shutil,subprocess,os,time
H=Path(__file__).resolve().parent;ROOT=H.parents[5];B=H/'isolated';LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
assert json.loads((H/'EXTRA-CONTROL-v1.json').read_text())['status']=='EXTRA-CONTROL-PASS'
modules=json.loads((H/'SOURCE-ADOPTION-v2.json').read_text())['order'];stored=json.loads((H/'STORED-OCCURRENCE-INDEX-v4.json').read_text());expected=[(p['producer'],i,n) for p in stored['producers'] for i,n in enumerate(p['extraConstNames'])]
(H/'EXTRA-CANDIDATE-TIMING-PLAN-v1.json').write_text(json.dumps({'writtenUTC':datetime.now(timezone.utc).isoformat(),'fixedOccurrences':704,'controlQuerySeconds':0.7947933340001327,'projectionSeconds':5,'perProcessCap':60},indent=2)+'\n')
shutil.copyfile(H/'CompilerExtras.lean',B/'CompilerExtras.lean');(B/'ProbeCompilerExtras.lean').write_text('import CompilerExtras\nimport ConsumerControls\n#sol_compiler_extras "'+','.join(modules)+'"\n');records=[]
for label,args in [('compile-CompilerExtras-candidate',['-o','CompilerExtras.olean','CompilerExtras.lean']),('compiler-extras-candidate',['ProbeCompilerExtras.lean'])]:
 t=time.perf_counter();r=subprocess.run([str(LEAN),*args],cwd=B,env={**os.environ,'LEAN_PATH':str(B)},stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=60);(H/(label+'-v1.log')).write_text(r.stdout);records.append({'label':label,'exit':r.returncode,'seconds':time.perf_counter()-t});assert r.returncode==0,label
rows=[json.loads(l[6:]) for l in (H/'compiler-extras-candidate-v1.log').read_text().splitlines() if l.startswith('EXTRA\t')];assert [(r['producer'],r['occurrenceIndex'],r['name']) for r in rows]==expected;assert len(rows)==704 and len({r['name'] for r in rows})==704
assert all(r['resolvedOrigin']==r['producer'] for r in rows),'undecidable/compiler-origin attribution'
visible=[r for r in rows if r['hasKernelConstantInfo']]
names={r['stored']['name'] for r in stored['occurrences']};assert all(r['name'] in names for r in visible),'new kernel-visible helper lacks body audit'
out={'status':'COMPILER-EXTRA-ORIGIN-METADATA-PASS','occurrences':704,'uniqueNames':704,'kernelVisibleInAlreadyAuditedStoredTable':len(visible),'kernelInvisibleNames':704-len(visible),'rows':rows,'processes':records,'scope':'Every actual ModuleData.extraConstNames producer occurrence and resolved origin; kernel-invisible compiler names have no ConstantInfo kind/type/body to inspect, are not kernel axiom declarations, and are not a machine-semantics proof.'};(H/'COMPILER-EXTRA-AUDIT-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='rows'}))
