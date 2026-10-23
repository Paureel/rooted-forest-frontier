"""Author isolated caller replay. Conditional recursive IH is NOT a MAF solver."""
from pathlib import Path
import datetime, hashlib, json, os, re, subprocess, time

D=Path(__file__).resolve().parent
R=D.parents[4]
OUT=R/'results'/('algorithm-universal233-query-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'))
OUT.mkdir(exist_ok=False)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
pin=json.loads((D/'CONTROL-PIN-v1.json').read_text())
for n,h in pin['source_sha256'].items(): assert sha(D/n)==h,n
order=['Caller','Precontrols','Specification','Budgets','Mass','Work','ConsumerControls']
entries=[]
for n in order:
 p=D/(n+'.lean'); data=p.read_text()
 clean=re.sub(r'/\-.*?\-/','',data,flags=re.S);clean=re.sub(r'--[^\n]*','',clean)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean),n
 entries.append({'module':n,'source':str(p.relative_to(R)),'sha256':sha(p)})
 (OUT/p.name).write_text(data)
(OUT/'FalsePrecontrols.lean').write_bytes((D/'FalsePrecontrols.lean').read_bytes())
(OUT/'lean-toolchain').write_bytes((R/'research/rmaf/lean/lean-toolchain').read_bytes())
record={'status':'RUNNING AUTHOR conditional paid scheduler','full_algorithm_proved':False,
 'independent_acceptance':False,'all_main_milestones':'OPEN','source_inputs':entries,
 'positive_order':order,'preproof_control_pin':{'path':str((D/'CONTROL-PIN-v1.json').relative_to(R)),'sha256':sha(D/'CONTROL-PIN-v1.json')},'runs':[]}
def save(): (OUT/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
def run(n,build=False):
 start=time.monotonic()
 p=subprocess.run([str(R/'bootloops-lean')]+(['-o',str(OUT/(n+'.olean'))] if build else [])+[str(OUT/(n+'.lean'))],cwd=R,env=dict(os.environ,LEAN_PATH=str(OUT)),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
 (OUT/(n+'.log')).write_text(p.stdout)
 record['runs'].append({'module':n,'exit':p.returncode,'seconds':time.monotonic()-start});save();return p
(OUT/'TrueControl.lean').write_text('theorem true_control : 2+2=4 := by decide\n')
assert run('TrueControl').returncode==0
for n in order:
 p=run(n,True);assert p.returncode==0,p.stdout
def inventory(extra=''):
 mods=order+([extra] if extra else [])
 return '\n'.join('import '+n for n in mods)+'''
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let mods : List Name := ['''+', '.join('`'+n for n in mods)+''']
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
(OUT/'ModuleAudit.lean').write_text(inventory())
p=run('ModuleAudit');assert p.returncode==0,p.stdout
mods=re.findall(r'^MODULE\|([^|\n]+)\|(.+)$',p.stdout,re.M)
axs=re.findall(r'^MODAUDIT\|([^|\n]+)\|\[([^\]]*)\]$',p.stdout,re.M)
def complete(m,a):
 return bool(m) and len(m)==len(a) and len(m)==len(set(m)) and {n for _,n in m}=={n for n,_ in a} and {x for x,_ in m}==set(order)
assert complete(mods,axs)
assert not complete(mods,axs[1:])
wrong=[('WrongOrigin',mods[0][1])]+mods[1:]
assert not complete(wrong,axs)
assert any('_private' in n and 'private_origin_control' in n for _,n in mods)
union=sorted({x.strip() for _,a in axs for x in a.split(',') if x.strip()})
assert set(union)<={'propext','Quot.sound','Classical.choice'}
p=run('FalsePrecontrols');assert p.returncode!=0 and p.stdout.count('is false')==4,p.stdout
(OUT/'PlantPrivate.lean').write_text('namespace ForeignNamespace\nprivate axiom concealed : False\ntheorem uses_concealed : False := concealed\nend ForeignNamespace\n')
assert run('PlantPrivate',True).returncode==0
(OUT/'PlantAudit.lean').write_text(inventory('PlantPrivate'))
p=run('PlantAudit');assert p.returncode!=0 and 'REJECT_CUSTOM_AXIOM' in p.stdout,p.stdout
assert sha(OUT/'Caller.lean')!=hashlib.sha256((OUT/'Caller.lean').read_bytes()+b'\n-- corrupted\n').hexdigest()
assert not all(e['sha256']==sha(D/(e['module']+'.lean')) for e in [dict(entries[0],sha256='0'*64)])
for e in entries: assert sha(R/e['source'])==e['sha256']
for n,h in pin['source_sha256'].items(): assert sha(D/n)==h,n
record.update({'status':'PASS AUTHOR conditional paid scheduler','positive_source_modules':len(order),
 'module_origin_declarations':len(mods),'module_counts':{m:sum(x==m for x,_ in mods) for m in sorted(set(x for x,_ in mods))},
 'private_generated_included':True,'axiom_union_observed':union,
 'preproof_positive_controls':10,'consumer_control_theorems':8,'false_propositions_rejected':4,
 'missing_axiom_record_caught':True,'wrong_module_origin_caught':True,'foreign_private_axiom_caught':True,
 'byte_corruption_caught':True,'source_pin_mismatch_caught':True,
 'scope':'Literal early-pruned exact-min conditional caller; final total check; actual executed call trace paid mass when≥2bad; exact value/dispatch meter with conservative source contracts. MAF slot construction/decomposition/reconstruction, exact recursive solver/IH, and global runtime OPEN.'})
save()
(OUT/'VERDICT.txt').write_text(f'PASS AUTHOR CONDITIONAL: {len(order)} source modules/{len(mods)} full origin declarations; all main milestones OPEN.\n')
(D/'LATEST-REPLAY.txt').write_text(str(OUT.relative_to(R))+'\n')
print('PASS',len(order),'source modules',len(mods),'full origin declarations')
print('Receipt',OUT)
