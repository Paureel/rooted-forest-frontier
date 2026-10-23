"""One-shot source-bound finite extension audit; author evidence only.
Extends the frozen module-origin audit design; never writes frozen originals.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,time,datetime
D=Path(__file__).resolve().parent;ROOT=D.parents[4];old=D.parent/'scaffold-proof';stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ');out=D/'replay'/stamp;out.mkdir(parents=True,exist_ok=False)
inputs=[old/(n+'.lean') for n in ['RMAF','CoreGraph','CoreProgram','PairWitness']]+[D/'ClusterFreeWitness.lean',D/'FalseClusterFree.lean']
hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
for p in inputs:(out/p.name).write_bytes(p.read_bytes())
(out/'lean-toolchain').write_bytes((ROOT/'research/rmaf/lean/lean-toolchain').read_bytes())
(out/'ModuleAudit.lean').write_text('''import ClusterFreeWitness
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let mods : List Name := [`RMAF, `CoreGraph, `CoreProgram, `PairWitness, `ClusterFreeWitness]
 let names := (((env.constants.map₁.toList ++ env.constants.map₂.toList).map (·.1)).filter fun n =>
   match env.getModuleIdxFor? n with
   | some i => mods.contains env.header.moduleNames[i.toNat]!
   | none => false).eraseDups
 for n in names do
   let some i := env.getModuleIdxFor? n | throwError "missing module"
   logInfo m!"MODULE|{env.header.moduleNames[i.toNat]!}|{n}"
   let ax ← collectAxioms n
   logInfo m!"MODAUDIT|{n}|{ax.toList}"
   for a in ax do
     unless a == `propext || a == `Quot.sound || a == `Classical.choice do
       throwError m!"REJECT_CUSTOM_AXIOM|{n}|{a}"
''')
env=os.environ.copy();env['LEAN_PATH']=str(out);runs=[]
def run(n,build=False):
 start=time.monotonic();p=subprocess.run([str(ROOT/'bootloops-lean')]+(['-o',str(out/(n+'.olean'))] if build else [])+[str(out/(n+'.lean'))],cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30);(out/(n+'.log')).write_text(p.stdout);runs.append({'module':n,'exit':p.returncode,'seconds':time.monotonic()-start});return p
for n in ['RMAF','CoreGraph','CoreProgram','PairWitness','ClusterFreeWitness']:
 p=run(n,True)
 if p.returncode:raise SystemExit(p.stdout)
p=run('ModuleAudit');assert p.returncode==0,p.stdout
mods=re.findall(r'^MODULE\|([^|]+)\|(.+)$',p.stdout,re.M);axs=re.findall(r'^MODAUDIT\|([^|]+)\|\[(.*?)\]$',p.stdout,re.M);assert mods and len(mods)==len(axs) and {n for _,n in mods}=={n for n,_ in axs}
p=run('FalseClusterFree');assert p.returncode!=0 and p.stdout.count('is false')==3,p.stdout
for p in inputs:assert hashlib.sha256(p.read_bytes()).hexdigest()==hashes[str(p.relative_to(ROOT))]
record={'status':'PASS-author-finite-extension-only','input_hashes':hashes,'runs':runs,'module_origin_count':len(mods),'module_counts':{n:sum(m==n for m,_ in mods) for n in sorted({m for m,_ in mods})},'false_propositions_rejected':3,'production_cut_correspondence_qualification':'PAIR-FIRE-ERRATUM-v2.md;2/9 prototype choices are alternate actual cuts with same partition/cost. Frozen production source/color assertions retain printed scope.','scope':'Kernel checks exact14-label proper common-cluster absence,3 paid target-disjoint partitions,1 bad local parent per output, exhaustive actual-label two-tag failure. Not independent verification or universal algorithm.'};(out/'certificate.json').write_text(json.dumps(record,indent=2)+'\n');(D/'LATEST-LEAN-REPLAY.txt').write_text(str(out)+'\n');print(json.dumps(record,indent=2))
