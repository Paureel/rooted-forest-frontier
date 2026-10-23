"""One-shot source-bound AUTHOR replay and complete module-origin axiom audit.
Not a nonauthor semantic/consumer review. The compilable axiom plant must fail
this audit even for its deliberately unreferenced axiom declaration.
"""
from pathlib import Path
import subprocess,json,time,hashlib,re,os,datetime,shutil
ROOT=Path(__file__).resolve().parents[5];BASE=Path(__file__).resolve().parent;SRC=BASE/'lean'
OUT=ROOT/'research/rmaf/results/algorithm-pair-case-geometry-formal-v1.json'
if OUT.exists():raise FileExistsError(OUT)
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ');DEST=BASE/'replay'/stamp;DEST.mkdir(parents=True,exist_ok=False)
positive=['RMAF','Geometry','Bridge','Selector','Controls'];negative=['FalseSharedThree','FalseRootUp','FalseSuppressed','FalseClear','FalseAbsent']
for name in positive+negative+['Audit','CustomAxiom','AuditCustom']:
 shutil.copyfile(SRC/(name+'.lean'),DEST/(name+'.lean'))
for name in positive:
 assert not re.search(r'\b(?:sorry|admit|native_decide)\b|(?m:^\s*axiom\b)',(DEST/(name+'.lean')).read_text()),name
frozen=json.loads((ROOT/'research/rmaf/algorithm/universal233/geometry/certificate.json').read_text())['sources_sha256']
imports={'RMAF':'research/rmaf/lean/RMAF.lean','Geometry':'research/rmaf/algorithm/universal233/geometry/Geometry.lean','Bridge':'research/rmaf/algorithm/universal233/geometry/Bridge.lean'}
for name,path in imports.items():
 assert (DEST/(name+'.lean')).read_bytes()==(ROOT/path).read_bytes()
 assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==frozen[path]
env=dict(os.environ,LEAN_PATH=str(DEST));rows=[];begin=time.perf_counter()
def run(name,compile=False):
 cmd=[str(ROOT/'bootloops-lean')]
 if compile:cmd+=['-o',str(DEST/(name+'.olean'))]
 cmd+=[str(DEST/(name+'.lean'))];t=time.perf_counter();p=subprocess.run(cmd,cwd=ROOT,env=env,capture_output=True,text=True)
 txt=p.stdout+p.stderr;(DEST/(name+'.log')).write_text(txt)
 row={'module':name,'exit':p.returncode,'seconds':time.perf_counter()-t,'log':str((DEST/(name+'.log')).relative_to(ROOT))};rows.append(row)
 return p.returncode,txt
for name in positive:
 code,txt=run(name,True);assert code==0,(name,txt)
code,txt=run('Audit');assert code==0,txt
def parse(text):
 result={}
 for line in text.splitlines():
  if not line.startswith('ORIGIN-AUDIT|'):continue
  _,origin,name,isaxiom,axioms=line.split('|',4)
  assert name not in result,name
  result[name]={'origin':origin,'is_axiom':isaxiom=='true','axioms':sorted(x for x in axioms.split(',') if x)}
 return result
allowed={'propext','Classical.choice','Quot.sound'}
def reject(rows):return {n:d for n,d in rows.items() if d['is_axiom'] or not set(d['axioms'])<=allowed}
audit=parse(txt);assert set(d['origin'] for d in audit.values())==set(positive)
assert not reject(audit),reject(audit)
for name in negative:
 code,txt=run(name);assert code!=0 and 'proved that the proposition' in txt and 'is false' in txt,(name,txt)
code,txt=run('CustomAxiom',True);assert code==0,txt
code,txt=run('AuditCustom');assert code==0,txt
custom=parse(txt);bad=reject(custom)
assert any(n.endswith('audit_plant_not_referenced') and d['is_axiom'] for n,d in bad.items())
assert any(n.endswith('unused_selector_escape') and d['is_axiom'] for n,d in bad.items())
assert any(n.endswith('counterfeit_selector') and d['axioms'] for n,d in bad.items())
for p in SRC.glob('*.lean'):
 if p.stem in positive+negative+['Audit','CustomAxiom','AuditCustom']:assert p.read_bytes()==(DEST/p.name).read_bytes()
version=subprocess.run([str(ROOT/'bootloops-lean'),'--version'],cwd=ROOT,capture_output=True,text=True);assert version.returncode==0
counts={m:sum(d['origin']==m for d in audit.values()) for m in positive}
result={'scope':'Actual original-address G selector, region-degree and executable soundness/completeness; AUTHOR-CHECKED pending nonauthor consumer review. All3main milestones OPEN.',
 'compiler':version.stdout.strip(),'source_bound_replay':str(DEST.relative_to(ROOT)),'builds':rows,'complete_module_origin_audit':audit,'module_origin_declaration_counts':counts,
 'new_explicit_theorems':{m:len(re.findall(r'(?m)^theorem\s+', (DEST/(m+'.lean')).read_text())) for m in ['Selector','Controls']},
 'false_propositions_rejected':negative,'compilable_custom_axiom_control_rejected_by_audit':bad,
 'imported_frozen_source_hashes':{p:frozen[p] for p in imports.values()},
 'source_sha256':{str((SRC/(n+'.lean')).relative_to(ROOT)):hashlib.sha256((SRC/(n+'.lean')).read_bytes()).hexdigest() for n in positive+negative+['Audit','CustomAxiom','AuditCustom']},
 'seconds':time.perf_counter()-begin}
OUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'declarations_by_module':counts,'new_explicit_theorems':result['new_explicit_theorems'],'false_controls':len(negative),'custom_axiom_bad_declarations':len(bad),'seconds':result['seconds'],'receipt':str(OUT)}))
