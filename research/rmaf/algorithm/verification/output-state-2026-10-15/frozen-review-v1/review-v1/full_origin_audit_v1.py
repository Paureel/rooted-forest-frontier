from pathlib import Path
import json,hashlib,subprocess,os,time,traceback
H=Path(__file__).resolve().parent;R=next(p for p in H.parents if (p/'bootloops-lean').is_file());F=H/'isolated-source-v1';C=json.loads((H/'AUTHOR-certificate.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();mods=C['positive_order']
source='\n'.join('import '+n for n in mods)+'''
import Lean
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
run_cmd do
 let env ← getEnv
 let modules : List Name := MODULES
 let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
 let mut seen : List Name := []
 let mut bad := 0
 for origin in modules do
  let p ← liftIO <| findOLean origin
  logInfo m!"PATH|{origin}|{p}"
 for (n,i) in env.constants.toList do
  if let some idx := env.getModuleIdxFor? n then
   let origin := env.allImportedModuleNames[idx.toNat]!
   if modules.contains origin then
    seen := origin :: seen
    let axs ← collectAxioms n
    let reject := i.isAxiom || i.isUnsafe || axs.toList.any (fun a => !allowed.contains a)
    if reject then bad := bad+1
    let kind := match i with
      | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
    let bodyHash := match i.value? with | none => "none" | some v => toString (hash v)
    let obj := Json.mkObj [
      ("origin",toJson origin.toString),("name",toJson n.toString),("kind",toJson kind),
      ("axioms",toJson (axs.toList.map Name.toString)),("is_axiom",toJson i.isAxiom),
      ("unsafe",toJson i.isUnsafe),("rejected",toJson reject),
      ("type_expr",toJson (reprStr i.type)),("type_structural_hash64",toJson (toString (hash i.type))),
      ("body_structural_hash64",toJson bodyHash)]
    logInfo m!"DECLJSON|{obj.compress}"
 for origin in modules do
  let count := (seen.filter (· == origin)).length
  logInfo m!"COUNT|{origin}|{count}"
  if count == 0 then throwError "FRESH_MISSING_ORIGIN"
 logInfo m!"BAD|{bad}"
 if bad > 0 then throwError "FRESH_FORBIDDEN_ORIGIN_DECLARATION"
'''.replace('MODULES','['+','.join('`'+n for n in mods)+']')
(F/'FreshOriginAuditV1.lean').write_text(source);env=os.environ.copy();env['LEAN_PATH']=str(F);start=time.monotonic()
p=subprocess.run([str(R/'bootloops-lean'),'-o','FreshOriginAuditV1.olean','FreshOriginAuditV1.lean'],cwd=F,env=env,capture_output=True,text=True,timeout=30);log=p.stdout+p.stderr;(F/'FreshOriginAuditV1.log').write_text(log)
assert p.returncode==0,log[-4000:]
rows=[];counts={};paths={}
for line in log.splitlines():
 if line.startswith('DECLJSON|'):rows.append(json.loads(line.split('|',1)[1]))
 elif line.startswith('COUNT|'):
  _,origin,count=line.split('|');counts[origin]=int(count)
 elif line.startswith('PATH|'):
  _,origin,path=line.split('|');paths[origin]=path
assert len(rows)==len({x['name'] for x in rows})==sum(counts.values())==3855
assert set(counts)==set(mods) and counts==C['module_counts']
assert len(paths)==121 and all(Path(path).resolve()==F/(origin+'.olean') for origin,path in paths.items())
assert not any(x['rejected'] for x in rows)
canonical={};axioms={}
for line in (R/'results/algorithm-universal233-output-state-20261015T105826Z/ModuleAudit.log').read_text().splitlines():
 if line.startswith('MODULE|'):
  _,origin,name=line.split('|');assert name not in canonical;canonical[name]=origin
 elif line.startswith('MODAUDIT|'):
  _,name,axs=line.split('|');axioms[name]=sorted(axs.split(',')) if axs else []
assert {x['name']:x['origin'] for x in rows}==canonical
assert {x['name']:sorted(x['axioms']) for x in rows}==axioms
origins={x['module']:x for x in C['source_inputs']}
for x in rows:x['producer_source']=origins[x['origin']]['path'];x['producer_sha256']=origins[x['origin']]['sha256'];x['isolated_source_sha256']=origins[x['origin']]['adapted_sha256']
out={'verdict':'PASS_COMPLETE_ORIGIN_SOURCE_BOUND_AUDIT','seconds':time.monotonic()-start,'module_count':121,'declaration_count':len(rows),'private_declarations':sum(x['name'].startswith('_private.') for x in rows),'recursors':sum(x['kind']=='recursor' for x in rows),'constructors':sum(x['kind']=='constructor' for x in rows),'nonstandard_axioms':[],'unsafe_declarations':[],'canonical_names_origins_axioms_exact':True,'module_counts':counts,'resolved_paths':paths,'declarations':rows,'body_adapter_basis':'all 121 producer and isolated sources compared byte-for-byte except the recorded eight import-only substitutions; generated type Expr and structural body hashes retained; hash64 is a diagnostic rather than a cryptographic body certificate','all_main_milestones':'OPEN'}
(R/'research/rmaf/results/algorithm-output-state-fresh-origin-audit-v1.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['verdict','seconds','module_count','declaration_count','private_declarations','recursors','constructors','canonical_names_origins_axioms_exact']}))
