from pathlib import Path
import os,json,hashlib,subprocess,time
root=Path(__file__).resolve().parents[5];b=Path(__file__).resolve().parent;iso=b/'isolated';h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
modules=json.loads((b/'CANDIDATE-PIN.json').read_text())['positive_modules'];allowed={'propext','Classical.choice','Quot.sound'}
source='''import Lean
import WorkControls
open Lean Elab Command

def wholeReviewKind : ConstantInfo → String
 | .axiomInfo _ => "axiom"
 | .defnInfo _ => "definition"
 | .thmInfo _ => "theorem"
 | .opaqueInfo _ => "opaque"
 | .quotInfo _ => "quotient"
 | .inductInfo _ => "inductive"
 | .ctorInfo _ => "constructor"
 | .recInfo _ => "recursor"
run_cmd do
 let env ← getEnv
 let wanted := MODULES
 for (n,ci) in env.constants.toList do
  if let some idx := env.getModuleIdxFor? n then
   let origin := env.header.moduleNames[idx.toNat]!.toString
   if wanted.contains origin then
    let axs ← Lean.collectAxioms n
    let row := Json.mkObj [("name",toJson n.toString),("origin",toJson origin),("kind",toJson (wholeReviewKind ci)),("axioms",toJson (axs.map Name.toString))]
    logInfo m!"WHOLE_ORIGIN_ROW {row.compress}"
'''
env=os.environ.copy();env['LEAN_PATH']=str(iso)
def run(name,imports,wanted):
 s=source.replace('import WorkControls',imports).replace('MODULES',json.dumps(wanted));p=iso/(name+'.lean');p.write_text(s)
 t=time.monotonic();r=subprocess.run([str(root/'bootloops-lean'),name+'.lean'],cwd=iso,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30);log=b/(name+'.log');log.write_text(r.stdout);assert r.returncode==0,r.stdout
 rows=[json.loads(l.split('WHOLE_ORIGIN_ROW ',1)[1]) for l in r.stdout.splitlines() if 'WHOLE_ORIGIN_ROW ' in l]
 assert rows and len(rows)==len({r['name'] for r in rows})
 return rows,{'module':name,'seconds':time.monotonic()-t,'source_sha256':h(p),'log_sha256':h(log)}
def gate(rows,names):
 return len(rows)==len({r['name'] for r in rows}) and {r['name'] for r in rows}==names and all(r['kind']!='axiom' and set(r['axioms'])<=allowed for r in rows)
rows,build=run('WholeReviewInventory','import WorkControls',modules);names={r['name'] for r in rows};assert gate(rows,names)
assert not gate(rows[1:],names) and not gate(rows+[rows[0]],names)
plants,pbuild=run('WholeReviewPlantInventory','import WholeReviewUsed\nimport WholeReviewUnused',['WholeReviewUsed','WholeReviewUnused']);assert not gate(plants,{r['name'] for r in plants})
assert any(r['origin']=='WholeReviewUnused' and r['kind']=='axiom' and '_private.' in r['name'] for r in plants)
assert any(r['origin']=='WholeReviewUnused' and r['kind']=='theorem' and not r['axioms'] for r in plants)
assert any(r['origin']=='WholeReviewUsed' and 'hiddenBill' in r['name'] and '_private.' in r['name'] for r in plants)
clean,cbuild=run('WholeReviewCleanInventory','import WholeReviewClean',['WholeReviewClean']);assert gate(clean,{r['name'] for r in clean})
# Independent byte-level source-pin detector with clean/corrupt twins.
origin=json.loads((b/'CANDIDATE-PIN.json').read_text())['isolated_source_origins'][0];p=iso/Path(origin['path']).name;raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()==origin['sha256'];assert hashlib.sha256(raw+b'\n-- deliberate pin corruption\n').hexdigest()!=origin['sha256']
counts={m:sum(r['origin']==m for r in rows) for m in modules};assert all(counts.values())
x={'status':'PASS-COMPLETE-ORIGIN-AND-PLANTED-DETECTORS','total':len(rows),'module_counts':counts,'private_prefix_records':sum('_private.' in r['name'] for r in rows),'kind_counts':{k:sum(r['kind']==k for r in rows) for k in sorted({r['kind'] for r in rows})},'axiom_union':sorted({a for r in rows for a in r['axioms']}),'all_rows':rows,'plant_rows':plants,'clean_rows':clean,'builds':[build,pbuild,cbuild],'controls':{'clean':'ACCEPTED','missing_record':'REJECTED','duplicate_record':'REJECTED','private_used_custom_axiom':'REJECTED','private_unused_custom_axiom':'REJECTED','source_pin_corruption':'REJECTED-with-clean-twin'}}
(b/'ORIGIN-INVENTORY.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:v for k,v in x.items() if k not in ['all_rows','plant_rows','clean_rows']}))
