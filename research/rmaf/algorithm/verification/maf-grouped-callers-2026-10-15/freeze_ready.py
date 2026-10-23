"""Seal prerelease controls only; no author source discovery or compilation."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parents[5];HERE=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 for name in ('CONTROL-FREEZE-v1.json','ADDENDUM-FREEZE-v1.json','ADDENDUM-FREEZE-v2.json'):
  m=json.loads((HERE/name).read_text())
  for r in m['files']:assert sha(ROOT/r['path'])==r['sha256'],r['path']
 public=json.loads((HERE/'PUBLIC-STATE-SPAN-RECEIPT.json').read_text());assert sha(ROOT/public['source']['path'])==public['source']['sha256'];assert sha(ROOT/public['copy'])==public['span_sha256']
 prior=json.loads((HERE/'PRIOR-PRESERVATION-v1.json').read_text())['checks']
 for p in prior:
  m=ROOT/p['manifest'];assert sha(m)==p['sha256'];v=json.loads(m.read_text());assert len(v['files'])==p['files']
  for r in v['files']:assert sha(ROOT/r['path'])==r['sha256'],r['path']
 runtime={}
 for flag in ('--version','--print-prefix'):
  p=subprocess.run([str(ROOT/'bootloops-lean'),flag],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);assert p.returncode==0;runtime[flag]=p.stdout.strip()
 prefix=Path(runtime['--print-prefix']);paths=[ROOT/'bootloops-lean',ROOT/'bootloops-python',prefix/'bin/lean',prefix/'lib/lean/Std.olean',prefix/'lib/lean/Lean.olean',Path(sys.executable)]
 runtime['files']={str(p):{'realpath':str(p.resolve()),'sha256':sha(p)} for p in paths};(HERE/'RUNTIME-v1.json').write_text(json.dumps(runtime,indent=2)+'\n')
 base=ROOT/'research/rmaf/results';results=sorted(base.glob('algorithm-maf-grouped-prerelease-*.json'));receipts={p.name:json.loads(p.read_text()) for p in results}
 full=receipts['algorithm-maf-grouped-prerelease-full-v1.json'];assert full['status']=='PASS_PREPARATION_CONTROLS' and full['positive_checks']==389 and full['negative_catches']==40
 add=receipts['algorithm-maf-grouped-prerelease-addendum-v2.json'];assert add['status'].startswith('PASS_') and add['public_runtime_cases']==14 and add['false_catches']==4
 toy=receipts['algorithm-maf-grouped-prerelease-toy-gates-v1.json'];assert toy['negative_custom_axiom_catches']==3 and toy['explicit_false_prop_catches']==1
 assert all(r['candidate_contact']==False for r in receipts.values())
 files=sorted([p for p in HERE.rglob('*') if p.is_file() and '__pycache__' not in p.parts and not p.name.startswith('READY-MANIFEST-')]+results)
 assert len(files)==len(set(files));rows=[{'path':str(p.relative_to(ROOT)),'realpath':str(p.resolve()),'sha256':sha(p),'bytes':p.stat().st_size} for p in files]
 manifest={'version':1,'stage':'READY_PRE_CANDIDATE','utc':datetime.now(timezone.utc).isoformat(),'immutable':True,'candidate_contact':False,'candidate_compilation':False,'root_release_pending':True,'author_contacts':0,'preparation_children':0,'all_main_milestones':'OPEN','replication_count_added':0,'same_graph_checker_lineage':True,'prior_preservation':prior,'public_state_definition_contact':public,'runtime':runtime,'accepted_full_controls':{'original_cases':14,'grouped_cases':11,'malformed_original_cases':8,'positive_checks':389,'false_catches':40,'max_enumerated_local_labels':4,'max_partitions':15},'accepted_addendum':'addendum_v2.py','superseded_weak_addendum_v1_records':['supplied-boolean-with-failed-feasible-query','residual-feasibility-is-not-minimum-attainment'],'all_versions_retained':True,'std_only_toys':{'custom_axiom_catches':3,'explicit_false_proposition_catches':1,'no_scientific_candidate_imports':True},'receipts':[{'path':str(p.relative_to(ROOT)),'sha256':sha(p),'status':receipts[p.name]['status'],'accepted_scope':'v1 addendum two weak records superseded; see explicit correction' if 'addendum-v1' in p.name else 'finite preparation only'} for p in results],'files':rows,'file_count':len(rows),'total_bytes':sum(r['bytes'] for r in rows)}
 out=HERE/'READY-MANIFEST-v1.json';assert not out.exists();out.write_text(json.dumps(manifest,indent=2)+'\n')
 for p in files:
  if p!=HERE/'TARGET-v1.md':p.chmod(0o444)
 out.chmod(0o444);print(json.dumps({'status':manifest['stage'],'manifest':str(out.relative_to(ROOT)),'sha256':sha(out),'files':len(rows),'bytes':manifest['total_bytes']}))
if __name__=='__main__':main()
