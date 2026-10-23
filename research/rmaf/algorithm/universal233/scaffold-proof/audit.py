"""One-shot source-bound finite scaffold witness Lean audit.
Reuses the completed nonauthor module-origin inventory design (documented
contact) so compiler-generated private declarations are included as well.
This author replay is not independent scientific verification.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
D=Path(__file__).resolve().parent;ROOT=D.parents[4]
assert (ROOT/'bootloops-lean').exists(),ROOT
assert (D/'RMAF.lean').read_bytes()==(ROOT/'research/rmaf/lean/RMAF.lean').read_bytes()
(D/'AxiomInventory.lean').write_text('''import PairWitness
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules : List Name := [`RMAF, `CoreGraph, `CoreProgram, `PairWitness]
  let ns := ((env.constants.map₁.toList ++ env.constants.map₂.toList).map (·.1)).filter fun n =>
    match env.getModuleIdxFor? n with
    | some idx => modules.contains env.header.moduleNames[idx.toNat]!
    | none => false
  let ns := ns.eraseDups
  for n in ns do
    let some idx := env.getModuleIdxFor? n | throwError "missing module"
    logInfo m!"MODULE|{env.header.moduleNames[idx.toNat]!}|{n}"
    let axs ← collectAxioms n
    logInfo m!"MODAUDIT|{n}|{axs.toList}"
    for a in axs do
      unless a == `propext || a == `Quot.sound || a == `Classical.choice do
        throwError m!"REJECT_CUSTOM_AXIOM|{n}|{a}"
''')
env=os.environ.copy();env['LEAN_PATH']=str(D);runs=[]
def run(name,build=False):
    cmd=[str(ROOT/'bootloops-lean')]+(['-o',name+'.olean'] if build else [])+[name+'.lean'];start=time.monotonic();p=subprocess.run(cmd,cwd=D,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30);(D/(name+'-replay.log')).write_text(p.stdout);runs.append({'module':name,'returncode':p.returncode,'seconds':time.monotonic()-start,'source_sha256':hashlib.sha256((D/(name+'.lean')).read_bytes()).hexdigest()});return p
for name in ['RMAF','CoreGraph','CoreProgram','PairWitness']:
 p=run(name,True);assert p.returncode==0,p.stdout
p=run('AxiomInventory');assert p.returncode==0,p.stdout
mods=re.findall(r'^MODULE\|([^|]+)\|(.+)$',p.stdout,re.M);audits=re.findall(r'^MODAUDIT\|([^|]+)\|\[(.*?)\]$',p.stdout,re.M)
assert mods and len(mods)==len(audits) and {n for _,n in mods}=={n for n,_ in audits}
axes=sorted({v.strip() for _,xs in audits for v in xs.split(',') if v.strip()});assert set(axes)<={'propext','Quot.sound','Classical.choice'}
p=run('FalsePairWitness');assert p.returncode!=0 and p.stdout.count('proved that the proposition')==2 and p.stdout.count('is false')==2,p.stdout
for name in ['RMAF','CoreGraph','CoreProgram','PairWitness']:
 s=(D/(name+'.lean')).read_text();assert not re.search(r'\b(sorry|admit|native_decide)\b',s)
files={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in D.glob('*.lean')}
record={'status':'PASS-author-source-bound-finite-controls-only','source_hashes':files,'runs':runs,'module_origin_count':len(mods),'module_counts':{m:sum(x==m for x,_ in mods) for m in sorted({m for m,_ in mods})},'axiom_union':axes,'false_propositions_rejected':2,'scope':'Concrete14-label source partition/disjointness and bad-parent controls; local6-label two-tag lower-bound control; exact old mass failure. No universal pair recurrence or complete algorithm accepted.'};(D/'certificate.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
