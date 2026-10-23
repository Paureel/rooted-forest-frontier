from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[7] if False else next(p for p in Path(__file__).resolve().parents if (p/'bootloops-python').is_file())
H=R/'research/rmaf/algorithm/verification/output-state-2026-10-15'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
prior=[
 ('pair-case-2026-10-15/frozen-review-v2',196,'59aaecf285bdbf2b1a98c869e21c32e35c191bd0140f055f32f7e497914cb8a2'),
 ('rank-restriction-2026-10-15/frozen-ready-v1',32,'b27e9a0401a36be36c05ba119acbad0055c9d56593aab868a70662f82472ab0e'),
 ('rank-restriction-2026-10-15/frozen-review-v1',372,'615411115f301b02da3fa082036048c6c95487d0ebc26d79faacbfa4adf9c685'),
 ('depth-one-2026-10-15/frozen-ready-v1',46,'bcff1ad2931ec9991cb5de7c09bf8afa44253484602e38aec95e6d508e3fb787'),
 ('depth-one-2026-10-15/frozen-review-v1',154,'efd0d5bbe74e4fa8b7e5b12b542b15412a86c4b116df4deec00a1529da24bd4f')]
checks=[]
for rel,count,wanted in prior:
 p=R/'research/rmaf/algorithm/verification'/rel/'MANIFEST.json';assert sha(p)==wanted,(rel,'manifest drift');d=json.loads(p.read_text());assert len(d['files'])==count
 bad=[name for name,pin in d['files'].items() if sha(p.parent/name)!=pin];assert not bad,(rel,bad)
 checks.append({'manifest':str(p.relative_to(R)),'sha256':wanted,'expected_count':count,'matched_count':count})
p=H/'frozen-inputs-v1/MANIFEST.json';assert sha(p)=='489dc3ea2d90a44f32c821ad10681fdb491072c1b6c12bbeccbacce278677b02';d=json.loads(p.read_text())
assert len(d['files'])==9
for row in d['files']:assert sha(R/row['path'])==row['sha256'],row['path']
for row in json.loads((H/'frozen-inputs-v1/DEPENDENCIES-v1.json').read_text())['dependencies']:assert sha(R/row['path'])==row['sha256'],row['path']
for name in ['independent_output_state_v1.py','controls-v1.json','guard-controls-v1.json','std_toy_gates_v1.py','own_paircase_dependency.py','PLAN-v1.md']:
 assert sha(H/'preparation-v1'/name)==sha(H/'frozen-inputs-v1'/name),name
out={'phase':'PRE-CANDIDATE','candidate_contacts':0,'prior_seals':checks,'prior_files_matched':sum(x['matched_count'] for x in checks),'frozen_input_files_matched':9,'frozen_input_manifest_sha256':sha(p),'source_and_control_adapters_byte_verified':True,'all_main_milestones':'OPEN'}
(R/'research/rmaf/results/algorithm-output-state-fresh-integrity-v2.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'prior_files_matched':out['prior_files_matched'],'frozen_inputs_matched':9,'candidate_contacts':0}))
