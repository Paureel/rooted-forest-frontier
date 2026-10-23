#!/usr/bin/env python3
# One-shot completeness extension: origin modules include compiler-private decls.
from pathlib import Path
import hashlib,json,os,re,subprocess,time
ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience');D=Path(__file__).resolve().parent;B=D/'rebuild'
source='''import CoreInvariants
import CherryCoarsening
import Lean
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules : List Name := [`RMAF, `CoreGraph, `CherryCoarsening, `CoreProgram, `CoreInvariants]
  let ns := (env.constants.map₁.toList ++ env.constants.map₂.toList).map (·.1)
  let ns := (ns.filter fun n =>
    match env.getModuleIdxFor? n with
    | some idx => modules.contains env.header.moduleNames[idx.toNat]!
    | none => false).eraseDups
  for n in ns do
    let some idx := env.getModuleIdxFor? n | throwError "missing module"
    let mod := env.header.moduleNames[idx.toNat]!
    logInfo m!"MODULE|{mod}|{n}"
  for n in ns do
    let axs ← collectAxioms n
    logInfo m!"MODAUDIT|{n}|{axs.toList}"
    for a in axs do
      unless a == `propext || a == `Quot.sound || a == `Classical.choice do
        throwError m!"REJECT_CUSTOM_AXIOM|{n}|{a}"
'''
(B/'ModuleInventory.lean').write_text(source)
(B/'PlantModel.lean').write_text('namespace HiddenModel\naxiom borrowed : False\nend HiddenModel\n')
plant='import PlantModel\n'+source.replace('`CoreInvariants]','`CoreInvariants, `PlantModel]')
(B/'ModulePlantAudit.lean').write_text(plant)
env=os.environ.copy();env['LEAN_PATH']=str(B)
def run(n,build=False):
    cmd=[str(ROOT/'bootloops-lean')]+(['-o',n+'.olean'] if build else [])+[n+'.lean']
    start=time.monotonic();p=subprocess.run(cmd,cwd=B,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=20)
    (B/(n+'.log')).write_text(p.stdout)
    return p,{'source':n+'.lean','source_sha256':hashlib.sha256((B/(n+'.lean')).read_bytes()).hexdigest(),'returncode':p.returncode,'seconds':time.monotonic()-start}
p,t=run('ModuleInventory');assert p.returncode==0,p.stdout
s=p.stdout
def parse(s):
    m=re.findall(r'^MODULE\|([^|]+)\|(.+)$',s,re.M);a=re.findall(r'^MODAUDIT\|([^|]+)\|\[(.*?)\]$',s,re.M)
    assert m and len(m)==len(a) and len(m)==len(set(m)) and {n for _,n in m}=={n for n,_ in a},'missing/duplicate module audit record'
    return m,a
m,a=parse(s)
try:parse(re.sub(r'^MODAUDIT\|[^\n]+\n','',s,count=1,flags=re.M))
except AssertionError:missing='CAUGHT'
else:raise AssertionError('missing audit record plant survived')
fresh=set(re.findall(r'^DECL\|(.+)$',(B/'FreshAudit.log').read_text(),re.M))
by={k:sum(mod==k for mod,_ in m) for k in sorted({mod for mod,_ in m})}
axs=sorted({v.strip() for _,xs in a for v in xs.split(',') if v.strip()})
p,tp=run('PlantModel',True);assert p.returncode==0,p.stdout
p,ta=run('ModulePlantAudit');assert p.returncode!=0 and 'REJECT_CUSTOM_AXIOM|HiddenModel.borrowed|HiddenModel.borrowed' in p.stdout,p.stdout
r={'status':'CONFIRMED','module_origin_count':len(m),'core_count':len(m)-by['RMAF'],'shared_dependency_count':by['RMAF'],'module_counts':by,'namespace_audit_count':len(fresh),'additional_private_generated_names':sorted({n for _,n in m}-fresh),'unmatched_namespace_names':sorted(fresh-{n for _,n in m}),'axiom_union_observed':axs,'missing_record_plant':missing,'custom_axiom_outside_namespace_plant':'CAUGHT','timings':[t,tp,ta]}
assert not r['unmatched_namespace_names'],r
(D/'module-inventory-verdict.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:v for k,v in r.items() if k not in ['additional_private_generated_names','timings']},indent=2))
