from pathlib import Path
import json,hashlib,datetime
root=Path(__file__).resolve().parents[5];b=Path(__file__).resolve().parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=root/'research/rmaf/algorithm/verification/core-work-2026-10-15/ARTIFACTS.json';assert h(old)=='61e9aaa274f9ac625939efc3315bf9aa93638435daa90ae039d41a5ebbc67455'
assert h(b/'core_ledger.py')=='1cdd44a66ee70b62c9291cc6c41102a3951ac952959a973c46674a9f54da54b3'
inputs=[p for p in (b/'frozen-inputs').iterdir() if p.is_file()]
files=[b/n for n in ['TARGET-v1.md','OPERATION-SPEC.md','caller_ledger.py','core_ledger.py','define_controls.py','CONTROL-PIN.json','KERNEL-GATES.json','freeze_preparation.py']]+inputs
contacts={'phase':'before candidate contact','permitted_contacts':[str(p.relative_to(root)) for p in files if p.suffix=='.md' or p.parent.name=='frozen-inputs'],'reused_instrument':{'path':'core_ledger.py','sha256':h(b/'core_ledger.py'),'origin':'prior independent core-work ledger, same reviewer lineage, zero extra replications'},'new_instrument':'caller_ledger.py finite original graph/BFS paths,callback and outer-list/dedup demands; no author/prover code reuse','prior_frozen_review_manifest_identity_only':h(old),'excluded_unread':['whole_source_work author source/COST-MODEL/controls/receipts/audit','live main/pair/rank/restriction/assembly','other reviewer work'],'preparation_children':0,'candidate_content_or_compilations':0}
(b/'SOURCE-CONTACTS.json').write_text(json.dumps(contacts,indent=2)+'\n');files.append(b/'SOURCE-CONTACTS.json')
freeze={'status':'FROZEN-BEFORE-ANY-INSTRUMENT-EXECUTION','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file_hashes':{str(p.relative_to(root)):h(p) for p in files},'declared_controls':json.loads((b/'CONTROL-PIN.json').read_text())['declared_controls'],'declared_plants':json.loads((b/'CONTROL-PIN.json').read_text())['declared_plants'],'independent_replications_added':0,'all_three_main_milestones':'OPEN'}
p=b/'PRE-CANDIDATE-FREEZE.json';p.write_text(json.dumps(freeze,indent=2)+'\n');print(json.dumps({'pinned_files':len(files),'controls':freeze['declared_controls'],'plants':freeze['declared_plants'],'freeze_sha256':h(p)}))
