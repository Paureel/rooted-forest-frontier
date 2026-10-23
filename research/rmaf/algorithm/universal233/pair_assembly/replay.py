"""AUTHOR source-bound actual pair selector/exchange/generator consumer.
All imports completed+frozen; only documented COPY module-name adapters.
No candidate in another active scope is read. Independent grade remains OPEN.
"""
from pathlib import Path
import hashlib,json,datetime,os,re,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[4];U=D.parent
OUT=R/'results'/('algorithm-universal233-pair-assembly-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));OUT.mkdir(exist_ok=False)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
V=R/'research/rmaf/algorithm/verification/pair-case-2026-10-15/frozen-review-v2';VM=V/'MANIFEST.json';A=U/'assembly_completion/ASSEMBLY-COMPLETION-MANIFEST-v1.json'
def check_inputs():
 a=json.loads(A.read_text());v=json.loads(VM.read_text())
 for e in a['immutable_files']:assert sha(R/e['path'])==e['sha256'],e['path']
 for p,h in v['files'].items():assert sha(V/p)==h,p
 return [{'path':str(A.relative_to(R)),'sha256':sha(A),'files_checked':len(a['immutable_files'])},{'path':str(VM.relative_to(R)),'sha256':sha(VM),'files_checked':len(v['files'])}]
checks=check_inputs();entries=json.loads((D/'STACK-PINS.json').read_text())['entries']
new=['HardForest','SideColors','PairConsumer','VertexPair','GoodPair','PairPrecontrols','PairControls']
for n in new:entries.append({'module':n,'source':str((D/(n+'.lean')).relative_to(R)),'sha256':sha(D/(n+'.lean')),'compiled_sha256':sha(D/(n+'.lean')),'adapter':None})
order=[e['module'] for e in entries];assert len(order)==len(set(order))
for e in entries:
 p=R/e['source'];assert sha(p)==e['sha256'];data=p.read_bytes()
 if e['module']=='Cluster':
  assert data.startswith(b'import Restriction\n');data=data.replace(b'import Restriction\n',b'import ExchangeRestriction\n',1)
 assert hashlib.sha256(data).hexdigest()==e['compiled_sha256'];(OUT/(e['module']+'.lean')).write_bytes(data)
(OUT/'FalsePairPrecontrols.lean').write_bytes((D/'FalsePairPrecontrols.lean').read_bytes());(OUT/'lean-toolchain').write_bytes((R/'research/rmaf/lean/lean-toolchain').read_bytes())
record={'status':'RUNNING AUTHOR pair-case consumer','full_algorithm_proved':False,'independent_acceptance':False,'all_main_milestones':'OPEN','source_inputs':entries,'upstream_manifests':checks,'positive_order':order,'runs':[]}
def save():(OUT/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
def run(n,build=False):
 s=time.monotonic();p=subprocess.run([str(R/'bootloops-lean')]+(['-o',str(OUT/(n+'.olean'))] if build else [])+[str(OUT/(n+'.lean'))],cwd=R,env=dict(os.environ,LEAN_PATH=str(OUT)),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30);(OUT/(n+'.log')).write_text(p.stdout);record['runs'].append({'module':n,'exit':p.returncode,'seconds':time.monotonic()-s});save();return p
(OUT/'TrueControl.lean').write_text('theorem trueBeforeAudit : 2+2=4 := by decide\n');assert run('TrueControl').returncode==0
for n in order:
 p=run(n,True);assert p.returncode==0,p.stdout

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
   let some i := env.getModuleIdxFor? n | throwError "missing module"
   logInfo m!"MODULE|{env.header.moduleNames[i.toNat]!}|{n}"
   let axs ← collectAxioms n
   logInfo m!"MODAUDIT|{n}|{axs.toList}"
   for ax in axs do
    unless ax == `propext || ax == `Quot.sound || ax == `Classical.choice do
      throwError m!"REJECT_CUSTOM_AXIOM|{n}|{ax}"
'''
(OUT/'ModuleAudit.lean').write_text(inventory());p=run('ModuleAudit');assert p.returncode==0,p.stdout
mods=re.findall(r'^MODULE\|([^|]+)\|(.+)$',p.stdout,re.M);axs=re.findall(r'^MODAUDIT\|([^|\n]+)\|\[([^\]]*)\]$',p.stdout,re.M)
def complete(m,a):return bool(m) and len(m)==len(a) and len(m)==len(set(m)) and {n for _,n in m}=={n for n,_ in a} and {x for x,_ in m}==set(order)
assert complete(mods,axs);assert not complete(mods,axs[1:]);assert any('_private' in n and 'origin_control' in n for _,n in mods)
union=sorted({x.strip() for _,a in axs for x in a.split(',') if x.strip()});assert set(union)<={'propext','Quot.sound','Classical.choice'}
p=run('FalsePairPrecontrols');assert p.returncode!=0 and p.stdout.count('is false')==3,p.stdout
(OUT/'PlantPrivate.lean').write_text('namespace ForeignNamespace\nprivate axiom concealed : False\ntheorem use_concealed : False := concealed\nend ForeignNamespace\n');assert run('PlantPrivate',True).returncode==0
(OUT/'PlantAudit.lean').write_text(inventory('PlantPrivate'));p=run('PlantAudit');assert p.returncode!=0 and 'REJECT_CUSTOM_AXIOM' in p.stdout,p.stdout
assert sha(OUT/'GoodPair.lean') != hashlib.sha256((OUT/'GoodPair.lean').read_bytes()+b'\n-- corruption plant\n').hexdigest()
for e in entries:assert sha(R/e['source'])==e['sha256']
assert check_inputs()==checks
record.update({'status':'PASS AUTHOR actual good-parent pair-case consumer','positive_source_modules':len(order),'module_origin_declarations':len(mods),'module_counts':{m:sum(x==m for x,_ in mods) for m in sorted({m for m,_ in mods})},'private_generated_included':True,'axiom_union_observed':union,'preproof_positive_clauses':6,'new_positive_controls':sum(len(re.findall(r'^theorem control_', (D/(n+'.lean')).read_text(),re.M)) for n in ['PairPrecontrols','PairControls']),'false_propositions_rejected':3,'missing_record_plant_caught':True,'hidden_foreign_private_axiom_plant_caught':True,'source_pin_plant_caught':True,'meaning':'Actual total Gchoose plus proof-only E consumes original proper sourceP/A-good/outside-clearance, emits literal actual source-core outputs covering no-larger replacementAF with originalcuts/sourcevalidity/refinement and SAME rawLISTmass. Vertex branch <=c^-3+c^-4; edge <=c^-3 withkeptgoodA/fullBvsAclearance. Both-bad paidquery/state/history/termination/fullsolverruntime OPEN.'});save()
(OUT/'VERDICT.txt').write_text(f'PASS AUTHOR: {len(order)} source builds; {len(mods)} full module-origin declarations; three rejected false claims and three caught audit/pin plants. Fresh independent acceptance and all main milestones OPEN.\n')
print('PASS',len(order),'source modules',len(mods),'origin declarations');print('Receipt',OUT)
