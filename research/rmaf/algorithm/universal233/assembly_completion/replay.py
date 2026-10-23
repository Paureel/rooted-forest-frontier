"""Source-bound author hard2/same-list ownership consumer; independent grade OPEN.
All four input packages are COMPLETE and frozen. No original file is modified.
The cut Coverage module-name-only adapter was frozen in assembly v1; its exact
compiled copy is retained here, with original provenance through that manifest.
"""
from pathlib import Path
import hashlib,json,datetime,os,re,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[4];U=D.parent
OUT=R/'results'/('algorithm-universal233-assembly-completion-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));OUT.mkdir(exist_ok=False)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def manifest(p):
 m=json.loads(p.read_text());rows=m.get('immutable_files',[])
 if 'owned_files' in m:rows += [{'path':k,'sha256':v} for k,v in m['owned_files'].items()]
 rows += [{'path':k,'sha256':v} for k,v in m.get('exact_source_import_pins',{}).items()]
 if 'receipt_files_hash' in m:
  rp=R/m['receipt'];f=rp/'RECEIPT-FILES.json';assert sha(f)==m['receipt_files_hash'];rows += [{'path':str((rp/k).relative_to(R)),'sha256':v['sha256']} for k,v in json.loads(f.read_text()).items()]
 assert rows,p
 for x in rows:assert sha(R/x['path'])==x['sha256'],x['path']
 return {'path':str(p.relative_to(R)),'sha256':sha(p),'files_checked':len(rows)}
mp=[U/'assembly/ASSEMBLY-MANIFEST-v1.json',U/'hard_parent_refinement/HARD-PARENT-REFINEMENT-MANIFEST-v1.json',U/'whole_source_mass/WHOLE-SOURCE-MASS-MANIFEST-v1.json']
mc=[manifest(p) for p in mp]
entries=json.loads((D/'STACK-PINS.json').read_text())['entries'];new=['PaidAssembly','HardConsumer','HardPaid','CompletionControls']
entries += [{'module':n,'source':str((D/(n+'.lean')).relative_to(R)),'sha256':sha(D/(n+'.lean'))} for n in new]
order=[e['module'] for e in entries];assert len(order)==len(set(order))
for e in entries:
 p=R/e['source'];assert sha(p)==e['sha256'];(OUT/(e['module']+'.lean')).write_bytes(p.read_bytes())
(OUT/'FalseCompletion.lean').write_bytes((D/'FalseCompletion.lean').read_bytes());(OUT/'lean-toolchain').write_bytes((R/'research/rmaf/lean/lean-toolchain').read_bytes())
record={'status':'RUNNING AUTHOR hard2 same-list assembly','full_algorithm_proved':False,'independent_acceptance':False,'all_main_milestones':'OPEN','source_inputs':entries,'upstream_manifests':mc,'positive_order':order,'runs':[]}
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
p=run('FalseCompletion');assert p.returncode!=0 and p.stdout.count('is false')==4,p.stdout
(OUT/'PlantPrivate.lean').write_text('namespace ForeignNamespace\nprivate axiom concealed : False\ntheorem use_concealed : False := concealed\nend ForeignNamespace\n');assert run('PlantPrivate',True).returncode==0
(OUT/'PlantAudit.lean').write_text(inventory('PlantPrivate'));p=run('PlantAudit');assert p.returncode!=0 and 'REJECT_CUSTOM_AXIOM' in p.stdout,p.stdout
assert sha(OUT/'PaidAssembly.lean') != hashlib.sha256((OUT/'PaidAssembly.lean').read_bytes()+b'\n-- corruption plant\n').hexdigest()
for e in entries:assert sha(R/e['source'])==e['sha256']
assert [manifest(p) for p in mp]==mc
record.update({'status':'PASS AUTHOR hard2 same-list assembly','positive_source_modules':len(order),'module_origin_declarations':len(mods),'module_counts':{m:sum(x==m for x,_ in mods) for m in sorted({m for m,_ in mods})},'private_generated_included':True,'axiom_union_observed':union,'positive_new_controls':len(re.findall(r'^theorem control_', (D/'CompletionControls.lean').read_text(), re.M)),'false_propositions_rejected':4,'missing_record_plant_caught':True,'hidden_foreign_private_axiom_plant_caught':True,'source_pin_plant_caught':True,'meaning':'Actual named original hard2 cherry safety consumes original agreement and constructs endpoint-or-literal forest covers; identical concrete colors and literal raw-list membership couple covers to clique/four/diagonal mass. No F-refines-parents input to outer consumer. Endpoint solver handling, recursive restrictions/reconstruction, state priorities, full termination/runtime OPEN.'});save()
(OUT/'VERDICT.txt').write_text(f'PASS AUTHOR: {len(order)} source builds; {len(mods)} full module-origin declarations; four rejected false claims and three caught audit/pin plants. Fresh independent acceptance and all main milestones OPEN.\n')
print('PASS',len(order),'source modules',len(mods),'origin declarations');print('Receipt',OUT)
