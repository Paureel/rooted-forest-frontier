#!/usr/bin/env python3
"""One-shot source-producer audit, constructed from Lean ModuleData API docs.

Author instrument, no independent review credit. It records stored producer
occurrences before coalescing and checks actual type/body reference closures.
"""
from pathlib import Path
import json,re,subprocess,os,hashlib,datetime,time
D=Path(__file__).resolve().parent;R=D.parents[4]
ALLOW={'Classical.choice','propext','Quot.sound'}

def audit_source(mods):
 return '\n'.join('import '+n for n in mods)+'''\nimport Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let expected : List Name := ['''+', '.join('`'+n for n in mods)+''']
 for i in [:env.header.moduleNames.size] do
   let producer := env.header.moduleNames[i]!
   let path ← liftIO <| findOLean producer
   logInfo m!"PATH|{producer}|{path}"
   if expected.contains producer then
     let data := env.header.moduleData[i]!
     unless data.constants.size == data.constNames.size do
       throwError m!"PRODUCER_NAME_LENGTH_MISMATCH|{producer}"
     logInfo m!"SUMMARY|{producer}|{data.constants.size}"
     for j in [:data.constants.size] do
       let ci := data.constants[j]!
       unless data.constNames[j]! == ci.name do
         throwError m!"PRODUCER_NAME_ROW_MISMATCH|{producer}|{j}"
       let kind := match ci with
         | .axiomInfo _ => "axiom"
         | .defnInfo _ => "definition"
         | .thmInfo _ => "theorem"
         | .opaqueInfo _ => "opaque"
         | .quotInfo _ => "quotient"
         | .inductInfo _ => "inductive"
         | .ctorInfo _ => "constructor"
         | .recInfo _ => "recursor"
       let resolved := match env.getModuleIdxFor? ci.name with
         | none => "UNATTRIBUTED"
         | some idx => toString env.header.moduleNames[idx.toNat]!
       if resolved == "UNATTRIBUTED" then
         throwError m!"UNATTRIBUTED_PRODUCER|{producer}|{ci.name}"
       let refs := ci.getUsedConstantsAsSet.toList
       let mut axs : List Name := []
       for dep in refs do
         let da ← collectAxioms dep
         axs := (axs ++ da.toList).eraseDups
       let row := Json.mkObj [
         ("producer",toJson (toString producer)),("index",toJson j),
         ("name",toJson (toString ci.name)),("resolved_origin",toJson resolved),
         ("kind",toJson kind),("type",toJson (reprStr ci.type)),
         ("body",toJson (ci.value?.map reprStr)),
         ("references",toJson (refs.map toString)),
         ("axiom_references",toJson (axs.map toString))]
       logInfo m!"PRODUCERJSON|{row.compress}"
       if kind == "axiom" then
         unless ci.name == `Classical.choice || ci.name == `propext || ci.name == `Quot.sound do
           throwError m!"REJECT_DIRECT_CUSTOM_AXIOM|{producer}|{j}|{ci.name}"
       for ax in axs do
         unless ax == `Classical.choice || ax == `propext || ax == `Quot.sound do
           throwError m!"REJECT_DEPENDENCY_CUSTOM_AXIOM|{producer}|{j}|{ci.name}|{ax}"
'''

def parse(log,mods,out):
 summaries=re.findall(r'^SUMMARY\|([^|]+)\|(\d+)$',log,re.M)
 assert len(summaries)==len(mods) and {m for m,n in summaries}==set(mods),'MISSING_OR_DUPLICATE_PRODUCER_SUMMARY'
 rows=[json.loads(s) for s in re.findall(r'^PRODUCERJSON\|(.*)$',log,re.M)]
 keys=[(r['producer'],r['index']) for r in rows]
 assert len(keys)==len(set(keys)),'DUPLICATE_PRODUCER_OCCURRENCE'
 expected={(m,i) for m,n in summaries for i in range(int(n))}
 assert set(keys)==expected,'MISSING_PRODUCER_OCCURRENCE'
 for row in rows:
  assert row['resolved_origin']!='UNATTRIBUTED'
  assert row['kind']!='axiom' or row['name'] in ALLOW,'DIRECT_CUSTOM_AXIOM'
  assert set(row['axiom_references'])<=ALLOW,'DEPENDENCY_CUSTOM_AXIOM'
 paths=dict(re.findall(r'^PATH\|([^|]+)\|(.+)$',log,re.M))
 assert set(mods)<=set(paths),'MISSING_MODULE_PATH'
 for m,p in paths.items():
  p=Path(p).resolve()
  assert p==(out/(m+'.olean')).resolve() if m in mods else p.is_relative_to(R/'.runtime/elan/toolchains'),'FOREIGN_MODULE_PATH'
 return rows,summaries,paths

def run_lean(out,name,build=False):
 p=subprocess.run([str(R/'bootloops-lean')]+(['-o',str(out/(name+'.olean'))] if build else [])+[str(out/(name+'.lean'))],
   cwd=out,env=dict(os.environ,LEAN_PATH=str(out)),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
 (out/(name+'.log')).write_text(p.stdout)
 return p

def detector_controls(out):
 (out/'CleanA.lean').write_text('import Std\ntheorem AuditShared : True := True.intro\n')
 (out/'CleanB.lean').write_text('import Std\ntheorem AuditShared : True := True.intro\ntheorem AuditOwn : (1:Nat)+1=2 := by decide\n')
 (out/'Hostile.lean').write_text('import Std\naxiom AuditShared : True\ntheorem AuditHostileOwn : (1:Nat)+1=2 := by decide\n')
 for n in ['CleanA','CleanB','Hostile']:
  p=run_lean(out,n,True);assert p.returncode==0,(n,p.stdout)
 (out/'CleanAudit.lean').write_text(audit_source(['CleanA','CleanB']))
 clean=run_lean(out,'CleanAudit');assert clean.returncode==0,clean.stdout
 rows,ss,ps=parse(clean.stdout,['CleanA','CleanB'],out)
 shared=[r for r in rows if r['name']=='AuditShared'];assert len(shared)==2 and len({r['producer'] for r in shared})==2
 (out/'HostileAudit.lean').write_text(audit_source(['CleanA','Hostile']))
 hostile=run_lean(out,'HostileAudit');assert hostile.returncode!=0 and 'REJECT_DIRECT_CUSTOM_AXIOM|Hostile|' in hostile.stdout,hostile.stdout
 checks={}
 for name,log in [('missing',re.sub(r'^PRODUCERJSON\|.*\n','',clean.stdout,count=1,flags=re.M)),
                  ('duplicate',clean.stdout+'PRODUCERJSON|'+json.dumps(rows[0])+'\n')]:
  try:parse(log,['CleanA','CleanB'],out)
  except AssertionError:checks[name]='CAUGHT'
  else:raise AssertionError('CORRUPTION_SURVIVED|'+name)
 return dict(clean_occurrences=len(rows),coalesced_shared_occurrences=len(shared),hostile_direct_axiom='CAUGHT',**checks)

if __name__=='__main__':
 out=R/'results'/('algorithm-universal233-rule5-local-producer-control-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));out.mkdir()
 (out/'lean-toolchain').write_bytes((D.parent/'cherry_branching/lean-toolchain').read_bytes())
 controls=detector_controls(out)
 (out/'certificate.json').write_text(json.dumps(dict(status='PASS_AUTHOR_DETECTOR_CONTROLS',controls=controls,
  instrument_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),post_contact=True),indent=2)+'\n')
 print('PASS_AUTHOR_DETECTOR_CONTROLS',out)
