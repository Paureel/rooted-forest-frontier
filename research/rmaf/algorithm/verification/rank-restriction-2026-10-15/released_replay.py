#!/usr/bin/env python3
"""One-shot released review driver. Reuses own G/E origin-audit API mechanism.
No author replay/checker code is imported or executed. Same reviewer lineage.
"""
import hashlib,json,os,subprocess,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=next(p for p in (HERE,*HERE.parents) if (p/'bootloops-lean').is_file())
RMAF=ROOT/'research/rmaf'
BUILD=HERE/'isolated-release-v1'
OUT=RMAF/'results/algorithm-rank-restriction-fresh-lean-gates-v1.json'
state={'phase':'RELEASED','scope':'Own preregistered detector gates first; no candidate positives compiled','runs':[],'audits':{}}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save():OUT.write_text(json.dumps(state,indent=2)+'\n')
def compile_one(folder,name,expected='compile'):
    env=os.environ.copy();env['LEAN_PATH']=str(folder)
    cmd=[str(ROOT/'bootloops-lean'),'-o',name+'.olean',name+'.lean']
    start=time.monotonic()
    try:
        p=subprocess.run(cmd,cwd=folder,env=env,capture_output=True,text=True,timeout=40);rc=p.returncode;log=p.stdout+p.stderr
    except subprocess.TimeoutExpired as ex:
        rc=124;log='OPEN:40-second timeout\n'+str(ex.stdout or '')+str(ex.stderr or '')
    (folder/(name+'.log')).write_text(log)
    state['runs'].append({'module':name,'directory':str(folder.relative_to(ROOT)),'command':cmd,'seconds':time.monotonic()-start,'returncode':rc,'expected':expected,'log_sha256':digest(folder/(name+'.log'))});save()
    print(json.dumps({k:state['runs'][-1][k] for k in ('module','seconds','returncode','expected')}),flush=True)
    if expected=='compile':assert rc==0,(name,log[-3000:])
    elif expected=='false':assert rc!=0 and 'decide' in log and 'proposition' in log and 'false' in log,(name,log[-3000:])
    else:assert rc!=0 and expected in log,(name,log[-3000:])
    return log
def audit_source(imports,modules):
    return '\n'.join('import '+x for x in imports)+'''
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let requested : List Name := MODULES
  if requested.isEmpty then throwError "FRESH_EMPTY_INVENTORY"
  let allowed : List Name := [`propext,`Classical.choice,`Quot.sound]
  let mut seen : List Name := []
  let mut bad : Nat := 0
  for (name,info) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let origin := env.allImportedModuleNames[index.toNat]!
      if requested.contains origin then
        seen := origin :: seen
        let axioms ← collectAxioms name
        let nonstandard := axioms.toList.filter (fun x => !allowed.contains x)
        let rejected := info.isAxiom || info.isUnsafe || !nonstandard.isEmpty
        if rejected then bad := bad + 1
        logInfo m!"FRESH|{origin}|{name}|{info.isAxiom}|{info.isUnsafe}|{String.intercalate "," (axioms.toList.map Name.toString)}|{rejected}"
  for origin in requested do
    let n := (seen.filter (· == origin)).length
    logInfo m!"FRESH_COUNT|{origin}|{n}"
    if n == 0 then throwError m!"FRESH_MISSING_ORIGIN {origin}"
  logInfo m!"FRESH_BAD|{bad}"
  if bad > 0 then throwError "FRESH_AUDIT_REJECT"
'''.replace('MODULES','['+','.join('`'+x for x in modules)+']')
def audit(folder,name,imports,modules,expected='compile'):
    (folder/(name+'.lean')).write_text(audit_source(imports,modules))
    log=compile_one(folder,name,expected);records=[];counts={}
    for line in log.splitlines():
        if line.startswith('FRESH|'):
            _,origin,n,isax,unsafe,axs,rejected=line.split('|')
            records.append({'origin':origin,'name':n,'is_axiom':isax=='true','unsafe':unsafe=='true','axioms':axs.split(',') if axs else [],'rejected':rejected=='true'})
        elif line.startswith('FRESH_COUNT|'):
            _,origin,n=line.split('|');counts[origin]=int(n)
    if expected not in ('FRESH_EMPTY_INVENTORY','FRESH_MISSING_ORIGIN'):
        assert records and set(counts)==set(modules) and sum(counts.values())==len(records)
        assert bool([r for r in records if r['rejected']])==(expected=='FRESH_AUDIT_REJECT')
    value={'counts':counts,'total':len(records),'bad':[r for r in records if r['rejected']],'all_declarations':records}
    state['audits'][folder.name+'/'+name]=value;save();return value
def own_gates():
    folder=BUILD/'own';assert not folder.exists();folder.mkdir(parents=True)
    pin=HERE/'frozen-ready-v1/LEAN-GATES-v1.json';state['preregistration_sha256']=digest(pin)
    (folder/'StdClean.lean').write_text('import Std\nprivate theorem hiddenClean : True := True.intro\ntheorem headlineClean : True := True.intro\n#print axioms headlineClean\n')
    (folder/'FalseControl.lean').write_text('import Std\ntheorem impossible : False := by decide\n')
    (folder/'CustomDependency.lean').write_text('import Std\naxiom unusedFalse : False\nprivate axiom privateFalse : False\nprivate theorem hiddenBad : False := privateFalse\ntheorem exportedBad : False := privateFalse\ntheorem cleanHeadline : True := True.intro\n')
    (folder/'ImportClient.lean').write_text('import CustomDependency\ntheorem importedBad : False := exportedBad\n#print axioms importedBad\n')
    cmd=[str(ROOT/'bootloops-lean'),'--version'];p=subprocess.run(cmd,capture_output=True,text=True,timeout=10);assert p.returncode==0
    (folder/'lean-version.log').write_text(p.stdout+p.stderr);state['actual_compiler']=p.stdout.strip();save()
    compile_one(folder,'StdClean');audit(folder,'CleanAudit',['StdClean'],['StdClean'])
    compile_one(folder,'FalseControl','false');compile_one(folder,'CustomDependency');compile_one(folder,'ImportClient')
    a=audit(folder,'CustomAudit',['ImportClient'],['CustomDependency','ImportClient'],'FRESH_AUDIT_REJECT')
    assert a['total']==6 and len(a['bad'])==5
    assert len([x for x in a['bad'] if x['is_axiom']])==2
    assert any(x['name'].startswith('_private.') for x in a['bad'])
    assert any(x['origin']=='ImportClient' for x in a['bad'])
    audit(folder,'EmptyAudit',['StdClean'],[],'FRESH_EMPTY_INVENTORY')
    audit(folder,'MissingAudit',['StdClean'],['StdClean','NeverImported'],'FRESH_MISSING_ORIGIN')
    state['verdict']='OWN-PREREGISTERED-LEAN-GATES-PASSED-BEFORE-CANDIDATE-POSITIVES';save()
if __name__=='__main__':
    try:own_gates()
    except Exception as ex:state['verdict']='OPEN-DETECTOR-FAILURE';state['error']=repr(ex);save();raise
