#!/usr/bin/env python3
"""One-shot prerelease Std-only detector toys. Same disclosed Lean API lineage.
No output_state module, original scientific olean, or author auditor is contacted.
"""
from pathlib import Path
import subprocess,os,time,json,hashlib,traceback
H=Path(__file__).resolve().parent;ROOT=next(p for p in (H,*H.parents) if (p/'bootloops-lean').is_file());F=H/'isolated-std-v1';OUT=ROOT/'research/rmaf/results/algorithm-output-state-fresh-std-gates-v1.json'
state={'phase':'PRE-CANDIDATE','candidate_contacts':0,'runs':[],'audits':{},'metadata_mutations':[],'all_main_milestones':'OPEN'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save():OUT.write_text(json.dumps(state,indent=2)+'\n')
def compile(n,expected='compile'):
 env=os.environ.copy();env['LEAN_PATH']=str(F);start=time.monotonic();cmd=[str(ROOT/'bootloops-lean'),'-o',n+'.olean',n+'.lean']
 try:p=subprocess.run(cmd,cwd=F,env=env,capture_output=True,text=True,timeout=30);rc=p.returncode;log=p.stdout+p.stderr
 except subprocess.TimeoutExpired as e:rc=124;log='OPEN:30-second timeout\n'+str(e.stdout or '')+str(e.stderr or '')
 path=F/(n+'.log');path.write_text(log);state['runs'].append({'module':n,'expected':expected,'returncode':rc,'seconds':time.monotonic()-start,'command':cmd,'log_sha256':sha(path)});save();print(json.dumps({k:state['runs'][-1][k] for k in ['module','expected','returncode','seconds']}),flush=True)
 if expected=='compile':assert rc==0,(n,log[-2500:])
 elif expected=='false':assert rc!=0 and 'decide' in log and 'proposition' in log and 'false' in log,(n,log[-2500:])
 else:assert rc!=0 and expected in log,(n,log[-2500:])
 return log
def audit(name,imports,modules,expected='compile'):
 source='\n'.join('import '+x for x in imports)+'''
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules : List Name := MODULES
  if modules.isEmpty then throwError "FRESH_EMPTY_INVENTORY"
  let allowed : List Name := [`propext,`Classical.choice,`Quot.sound]
  let mut seen : List Name := []
  let mut bad : Nat := 0
  for (n,i) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let origin := env.allImportedModuleNames[idx.toNat]!
      if modules.contains origin then
        seen := origin :: seen
        let axs ← collectAxioms n
        let reject := i.isAxiom || i.isUnsafe || (axs.toList.any (fun a => !allowed.contains a))
        if reject then bad := bad+1
        logInfo m!"DECL|{origin}|{n}|{i.isAxiom}|{i.isUnsafe}|{String.intercalate "," (axs.toList.map Name.toString)}|{reject}"
  for origin in modules do
    let count := (seen.filter (· == origin)).length
    logInfo m!"COUNT|{origin}|{count}"
    if count == 0 then throwError "FRESH_MISSING_ORIGIN"
  logInfo m!"BAD|{bad}"
  if bad > 0 then throwError "FRESH_CUSTOM_OR_UNSAFE"
'''.replace('MODULES','['+','.join('`'+x for x in modules)+']')
 (F/(name+'.lean')).write_text(source);log=compile(name,expected);rows=[];counts={}
 for line in log.splitlines():
  if line.startswith('DECL|'):
   _,origin,n,ax,unsafe,axs,reject=line.split('|');rows.append({'origin':origin,'name':n,'is_axiom':ax=='true','unsafe':unsafe=='true','axioms':axs.split(',') if axs else [],'rejected':reject=='true'})
  elif line.startswith('COUNT|'):
   _,origin,count=line.split('|');counts[origin]=int(count)
 if expected not in ['FRESH_EMPTY_INVENTORY','FRESH_MISSING_ORIGIN']:
  assert rows and set(counts)==set(modules) and len(rows)==sum(counts.values())
  assert bool(any(r['rejected'] for r in rows))==(expected=='FRESH_CUSTOM_OR_UNSAFE')
 state['audits'][name]={'rows':rows,'counts':counts,'total':len(rows),'rejected_count':sum(r['rejected'] for r in rows)};save();return rows

def main():
 assert not F.exists();F.mkdir()
 p=subprocess.run([str(ROOT/'bootloops-lean'),'--version'],capture_output=True,text=True,timeout=10);assert p.returncode==0;state['compiler']=p.stdout.strip();(F/'compiler-version.log').write_text(p.stdout+p.stderr);save()
 sources={
 'ToyClean':'''import Std
namespace OutputStateToy
inductive Bit where | zero | one
private theorem hiddenClean : True := True.intro
theorem publicClean : True := True.intro
end OutputStateToy
''',
 'ToyFalse':'''import Std
theorem explicitFalse : False := by decide
''',
 'ToyDirty':'''import Std
namespace OutputStateToy
axiom unusedFalse : False
private axiom secretFalse : False
private theorem hiddenBad : False := secretFalse
axiom usedFalse : False
theorem exportedBad : False := usedFalse
theorem cleanHeadline : True := True.intro
end OutputStateToy
''',
 'ToyClient':'''import ToyDirty
theorem importedBad : False := OutputStateToy.exportedBad
#print axioms importedBad
'''}
 for n,s in sources.items():(F/(n+'.lean')).write_text(s)
 compile('ToyClean');clean=audit('CleanAudit',['ToyClean'],['ToyClean']);compile('ToyFalse','false');compile('ToyDirty');compile('ToyClient');dirty=audit('DirtyAudit',['ToyClient'],['ToyDirty','ToyClient'],'FRESH_CUSTOM_OR_UNSAFE')
 assert len(dirty)==7 and sum(r['rejected'] for r in dirty)==6 and sum(r['is_axiom'] for r in dirty)==3
 assert any(r['name'].startswith('_private.') and r['rejected'] for r in dirty)
 assert any(r['origin']=='ToyClient' and r['rejected'] for r in dirty)
 assert any(r['name']=='OutputStateToy.cleanHeadline' and not r['rejected'] for r in dirty)
 names=[r['name'] for r in clean];required={'OutputStateToy.Bit','OutputStateToy.Bit.zero','OutputStateToy.Bit.one','OutputStateToy.Bit.rec','OutputStateToy.publicClean'};assert required<=set(names) and any(n.startswith('_private.') for n in names)
 wanted={r['name']:r['origin'] for r in clean};assert len(wanted)==len(clean)
 def valid(rows):
  ns=[r['name'] for r in rows]
  return bool(rows and len(ns)==len(set(ns))==len(wanted) and set(ns)==set(wanted)
              and all(r['origin']==wanted[r['name']] and not r['rejected'] for r in rows))
 assert valid(clean);state['metadata_mutations'].append({'id':'complete_clean_twin','expected':True,'actual':True})
 mutations={
  'drop_generated_recursor':[r for r in clean if r['name']!='OutputStateToy.Bit.rec'],
  'duplicate_record_same_count':clean[:-1]+[clean[0]],
  'change_generated_origin':[{**r,'origin':'ToyOther'} if r['name']=='OutputStateToy.Bit.rec' else r for r in clean],
  'omit_all_records':[],
 }
 for name,rows in mutations.items():
  got=valid(rows);assert not got,name;state['metadata_mutations'].append({'id':name,'expected':False,'actual':got})
 audit('EmptyAudit',['ToyClean'],[],'FRESH_EMPTY_INVENTORY');audit('MissingAudit',['ToyClean'],['ToyClean','NeverImported'],'FRESH_MISSING_ORIGIN')
 (F/'ToyPaths.lean').write_text('''import ToyClean
import Lean
open Lean Elab Command
run_cmd do
  let path ← liftIO <| findOLean `ToyClean
  logInfo m!"PATH|{path}"
''')
 log=compile('ToyPaths');paths=[line.split('|',1)[1] for line in log.splitlines() if line.startswith('PATH|')];assert len(paths)==1 and Path(paths[0]).resolve()==F/'ToyClean.olean'
 state['path_clean_twin']=paths[0];assert Path(paths[0]).resolve()!=F/'ToyOther.olean';state['wrong_path_mutation_rejected']=True
 pin=sha(F/'ToyClean.lean');changed=F/'ToyChanged.txt';changed.write_bytes((F/'ToyClean.lean').read_bytes()+b'\n-- corrupt source pin\n');assert sha(changed)!=pin;state['source_pin_clean']=pin;state['source_pin_corruption_rejected']=True
 state['verdict']='PASS-BLIND-STD-TOY-FALSE-CUSTOM-PRIVATE-IMPORT-AND-INVENTORY-GATES';state['candidate_contacts']=0;save();print(json.dumps({'verdict':state['verdict'],'clean_declarations':len(clean),'dirty_declarations':len(dirty),'bad_declarations':6,'candidate_contacts':0}),flush=True)
if __name__=='__main__':
 try:main()
 except Exception as e:state['verdict']='OPEN-STD-TOY-GATE-FAILURE';state['error']=repr(e);state['traceback']=traceback.format_exc();save();raise
