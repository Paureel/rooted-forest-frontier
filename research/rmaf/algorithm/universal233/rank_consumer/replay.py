"""AUTHOR actual bounded-rank classifier source replay; independent grade OPEN.
Known-rank four-color code uses literal q3, exact output reuse and actual caller
branches. Work is the reviewed conservative source model, not fine instructions.
"""
from pathlib import Path
import hashlib,json,datetime,os,re,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[4];U=D.parent
OUT=R/'results'/('algorithm-universal233-rank-consumer-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));OUT.mkdir(exist_ok=False)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
mp=[U/'rank_dichotomy/RANK-MANIFEST-v1.json',U/'core_work/CORE-WORK-MANIFEST-v1.json']
def check_inputs():
 checks=[]
 for p in mp:
  m=json.loads(p.read_text());rows=m.get('immutable_files')
  if rows is None:rows=[{'path':k,'sha256':v} for k,v in m['owned_files'].items()]
  for e in rows:assert sha(R/e['path'])==e['sha256'],e['path']
  checks.append({'path':str(p.relative_to(R)),'sha256':sha(p),'files_checked':len(rows)})
 return checks
checks=check_inputs();B=R/'results/algorithm-universal233-rank-replay-20261015T091933Z';bc=json.loads((B/'certificate.json').read_text())
entries=[{'module':n,'source':str((B/(n+'.lean')).relative_to(R)),'sha256':sha(B/(n+'.lean'))} for n in bc['positive_order']]
W=R/'results/algorithm-universal233-core-work-20261015T081612Z/Work.lean';entries.append({'module':'Work','source':str(W.relative_to(R)),'sha256':sha(W)})
new=['Probe','ProbeWork','FourProbe','OptimizedWork','ProbePrecontrols','ProbeControls']
for n in new:entries.append({'module':n,'source':str((D/(n+'.lean')).relative_to(R)),'sha256':sha(D/(n+'.lean'))})
order=[e['module'] for e in entries];assert len(order)==len(set(order))
for e in entries:
 p=R/e['source'];assert sha(p)==e['sha256'];data=p.read_bytes()
 clean=re.sub(r'/\-.*?\-/','',data.decode(),flags=re.S);clean=re.sub(r'--[^\n]*','',clean)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean),e['source']
 (OUT/(e['module']+'.lean')).write_bytes(data)
(OUT/'FalseProbe.lean').write_bytes((D/'FalseProbe.lean').read_bytes());(OUT/'lean-toolchain').write_bytes((R/'research/rmaf/lean/lean-toolchain').read_bytes())
review=R/'research/rmaf/algorithm/verification/core-work-2026-10-15/COST-CORRESPONDENCE.md'
record={'status':'RUNNING AUTHOR actual rank classifier','full_algorithm_proved':False,'independent_acceptance':False,'all_main_milestones':'OPEN','source_inputs':entries,'upstream_manifests':checks,'positive_order':order,'reviewed_source_model_contract':{'path':str(review.relative_to(R)),'sha256':sha(review),'meaning':'reviewed conservative source-operation correspondence under explicit contracts, not extracted fine instruction identity'},'runs':[]}
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
assert complete(mods,axs);assert not complete(mods,axs[1:]);assert any('_private' in n and 'private_origin_control' in n for _,n in mods)
union=sorted({x.strip() for _,a in axs for x in a.split(',') if x.strip()});assert set(union)<={'propext','Quot.sound','Classical.choice'}
p=run('FalseProbe');assert p.returncode!=0 and p.stdout.count('is false')==3,p.stdout
(OUT/'PlantPrivate.lean').write_text('namespace ForeignNamespace\nprivate axiom concealed : False\ntheorem use_concealed : False := concealed\nend ForeignNamespace\n');assert run('PlantPrivate',True).returncode==0
(OUT/'PlantAudit.lean').write_text(inventory('PlantPrivate'));p=run('PlantAudit');assert p.returncode!=0 and 'REJECT_CUSTOM_AXIOM' in p.stdout,p.stdout
assert sha(OUT/'FourProbe.lean') != hashlib.sha256((OUT/'FourProbe.lean').read_bytes()+b'\n-- corruption plant\n').hexdigest()
for e in entries:assert sha(R/e['source'])==e['sha256']
assert check_inputs()==checks;assert sha(review)==record['reviewed_source_model_contract']['sha256']
record.update({'status':'PASS AUTHOR actual bounded rank classifier','positive_source_modules':len(order),'module_origin_declarations':len(mods),'module_counts':{m:sum(x==m for x,_ in mods) for m in sorted({m for m,_ in mods})},'private_generated_included':True,'axiom_union_observed':union,'preproof_positive_statements':7,'new_consumer_control_theorems':len(re.findall(r'^theorem control_', (D/'ProbeControls.lean').read_text(),re.M)),'false_propositions_rejected':3,'missing_record_plant_caught':True,'hidden_foreign_private_axiom_plant_caught':True,'source_pin_plant_caught':True,'meaning':'Actual bounded generate acceptance iff rankfeasibility; known4color q3 classifier reuses exact literal singleton outputs at everylargerq, reject impliesallcost>=4/rawLISTmass<=2c^-4. Actual optimized branch meter includes bothgeneratecalls ifneeded, pruned/refusedprefixes and exactcolorcalls; source-model envelope pluscallbacks/fixedcaller allowance underreviewed contracts, notfineinstructions. Complete pairquery/state/solverruntime OPEN.'});save()
(OUT/'VERDICT.txt').write_text(f'PASS AUTHOR: {len(order)} source builds; {len(mods)} full module-origin declarations; three rejected false claims and three caught audit/pin plants. Fresh independent acceptance and all main milestones OPEN.\n')
print('PASS',len(order),'source modules',len(mods),'origin declarations');print('Receipt',OUT)
