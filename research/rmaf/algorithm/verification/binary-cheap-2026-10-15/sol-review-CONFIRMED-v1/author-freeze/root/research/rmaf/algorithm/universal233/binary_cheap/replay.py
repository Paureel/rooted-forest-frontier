"""One-shot binary-cheap AUTHOR source replay. Independent review remains OPEN.
Use completed frozen sources plus documented filename/import-only adapters.
"""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[4]
OUT=R/'results'/('algorithm-universal233-binary-cheap-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));OUT.mkdir(exist_ok=False)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_PIN_MISMATCH|'+str(p))
stack=json.loads((D/'STACK-PINS.json').read_text())
def check_upstream():
 out=[]
 for c in stack['manifests']:
  p=R/c['path'];pin(p,c['sha256']);m=json.loads(p.read_text());rows=m.get('immutable_files',m.get('entries',[]));assert len(rows)==c['checked']
  for e in rows:pin(R/e['path'],e['sha256'])
  out.append(c)
 return out
checks=check_upstream()
for v in ['v1','v2','v3']:
 m=json.loads((D/('CONTROLS-PIN-'+v+'.json')).read_text())
 # Earlier literal fixture versions and their failed logs remain separate.
 if v=='v3':
  for n,h in m['files'].items():pin(D/n,h)
pre=json.loads((D/'PREPROOF-RECEIPT-v1.json').read_text())
for n,h in pre['files'].items():pin(D/n,h)
entries=stack['entries'].copy()
new=['LiteralControls','BinaryEdge','CheapPartition','TargetGeometry','Continuation','LocalOne','PretestConsumer','SelectedContinuation','Symmetry','SelectedHigh','ConsumerControls']
for n in new:
 p=D/(n+'.lean');entries.append({'module':n,'path':str(p.relative_to(R)),'sha256':sha(p),'compiled_sha256':sha(p),'adapter':None})
order=[e['module'] for e in entries];assert len(set(order))==len(order)
for e in entries:
 p=R/e['path'];pin(p,e['sha256']);data=p.read_bytes()
 if e.get('adapter')=='first import Restriction->DepthRestriction':
  assert data.startswith(b'import Restriction\n');data=data.replace(b'import Restriction\n',b'import DepthRestriction\n',1)
 assert hashlib.sha256(data).hexdigest()==e.get('compiled_sha256',e['sha256'])
 clean=re.sub(r'/\-.*?\-/','',data.decode(),flags=re.S);clean=re.sub(r'--[^\n]*','',clean)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean),e['path']
 (OUT/(e['module']+'.lean')).write_bytes(data)
(OUT/'FalseLiteral.lean').write_bytes((D/'FalseLiteral.lean').read_bytes())
(OUT/'FalseLogic.lean').write_text('import ConsumerControls\ntheorem false_logic : False := by decide\n')
(OUT/'lean-toolchain').write_bytes((R/'research/rmaf/lean/lean-toolchain').read_bytes())
record={'status':'RUNNING_AUTHOR','all_three_main_milestones':'OPEN','full_algorithm_proved':False,'independent_acceptance':False,'source_operation_runtime_correspondence':'No new compiled/source-operation cost result. Value/graph/source-certificate and actual raw-list mass statements only.','upstream_manifests':checks,'source_inputs':entries,'positive_order':order,'preproof_receipt_sha256':sha(D/'PREPROOF-RECEIPT-v1.json'),'runs':[]}
def save():(OUT/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
def run(n,build=False):
 s=time.monotonic();p=subprocess.run([str(R/'bootloops-lean')]+(['-o',str(OUT/(n+'.olean'))] if build else [])+[str(OUT/(n+'.lean'))],cwd=R,env=dict(os.environ,LEAN_PATH=str(OUT)),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=45)
 (OUT/(n+'.log')).write_text(p.stdout);record['runs'].append({'module':n,'exit':p.returncode,'seconds':time.monotonic()-s});save();return p
(OUT/'TrueControl.lean').write_text('import Std\ntheorem true_control : (2 : Nat)+3=5 := by decide\n');assert run('TrueControl').returncode==0
for n in order:
 p=run(n,True);assert p.returncode==0 and 'declaration uses `sorry`' not in p.stdout,(n,p.stdout)
def inventory(extra=''):
 mods=order+([extra] if extra else []);imports='\n'.join('import '+n for n in mods);names=', '.join('`'+n for n in mods)
 return imports+'''\nimport Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let mods : List Name := ['''+names+''']
 let ns := (((env.constants.map₁.toList ++ env.constants.map₂.toList).map (·.1)).filter fun n =>
   match env.getModuleIdxFor? n with
   | some i => mods.contains env.header.moduleNames[i.toNat]!
   | none => false).eraseDups
 for n in ns do
   let some i := env.getModuleIdxFor? n | throwError "missing module origin"
   logInfo m!"MODULE|{env.header.moduleNames[i.toNat]!}|{n}"
   let axs ← collectAxioms n
   logInfo m!"MODAUDIT|{n}|{axs.toList}"
   for ax in axs do
    unless ax == `propext || ax == `Quot.sound || ax == `Classical.choice do
      throwError m!"REJECT_CUSTOM_AXIOM|{n}|{ax}"
'''
(OUT/'ModuleAudit.lean').write_text(inventory());p=run('ModuleAudit');assert p.returncode==0,p.stdout
mods=re.findall(r'^MODULE\|([^|]+)\|(.+)$',p.stdout,re.M);axs=re.findall(r'^MODAUDIT\|([^|\n]+)\|\[([^\]]*)\]$',p.stdout,re.M)
def complete(mm,aa):return bool(mm) and len(mm)==len(aa) and len(mm)==len(set(mm)) and {n for _,n in mm}=={n for n,_ in aa} and {x for x,_ in mm}==set(order)
assert complete(mods,axs);assert not complete(mods,axs[1:]);assert any('_private' in n and 'origin_control' in n for _,n in mods)
union=sorted({x.strip() for _,a in axs for x in a.split(',') if x.strip()});assert set(union)<={'propext','Quot.sound','Classical.choice'}
p=run('FalseLiteral');assert p.returncode!=0 and p.stdout.count('is false')==3,p.stdout
p=run('FalseLogic');assert p.returncode!=0 and 'is false' in p.stdout,p.stdout
(OUT/'PlantPrivate.lean').write_text('namespace ForeignNamespace\nprivate axiom concealed : False\ntheorem use_concealed : False := concealed\nend ForeignNamespace\n');assert run('PlantPrivate',True).returncode==0
(OUT/'PlantAudit.lean').write_text(inventory('PlantPrivate'));p=run('PlantAudit');assert p.returncode!=0 and 'REJECT_CUSTOM_AXIOM' in p.stdout,p.stdout
# Exercise the actual pin checker, with a clean twin, on a copied source.
f=OUT/'PinFixture.lean';f.write_bytes((D/'BinaryEdge.lean').read_bytes());h=sha(f);pin(f,h);f.write_bytes(f.read_bytes()+b'\n-- deliberate corruption\n')
try:pin(f,h)
except ValueError as e:assert 'SOURCE_PIN_MISMATCH' in str(e)
else:raise AssertionError('source corruption survived')
f.write_bytes((D/'BinaryEdge.lean').read_bytes());pin(f,h)
for e in entries:pin(R/e['path'],e['sha256'])
assert check_upstream()==checks
record.update({'status':'PASS_AUTHOR_SOURCE_BOUND_REPLAY','positive_source_modules':len(order),'module_origin_declarations':len(mods),'module_counts':{m:sum(x==m for x,_ in mods) for m in sorted({m for m,_ in mods})},'private_generated_included':True,'axiom_union_observed':union,'literal_preproof_controls':len(re.findall(r'^theorem control_', (D/'LiteralControls.lean').read_text(),re.M)),'postproof_consumer_controls':len(re.findall(r'^theorem control_', (D/'ConsumerControls.lean').read_text(),re.M)),'false_propositions_rejected':4,'missing_record_plant_caught':True,'foreign_private_axiom_plant_caught':True,'actual_source_pin_checker_corruption_caught_with_clean_twin':True,'meaning':'Scoped actual both-bad selected binary-edge cheap continuation, original-label q3 partition/source+targetvalidity, derived localminimum1/pretestoriginalLOCALcut, forallotheroutputkeptA/C+samecert+crossclear, otherwise2badactualdisjointcomponents, exactsameedgesymmetry, actualtwohighcosts/rawappendedLISTmass. Explicit paidqueryguard consumer; no fullsolver/sourcecutunion/globalrecurrence/runtime/novelty claim.'});save()
(OUT/'VERDICT.txt').write_text(f'PASS AUTHOR: {len(order)} source modules; {len(mods)} module-origin declarations; four false claims and all three audit/pin plants rejected. Fresh independent acceptance and all three main milestones OPEN.\n')
(D/'LATEST-REPLAY.txt').write_text(str(OUT)+'\n')
print('PASS',len(order),'source modules',len(mods),'origin declarations');print('Receipt',OUT)
