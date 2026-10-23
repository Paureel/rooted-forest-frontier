from pathlib import Path
import json,hashlib,re
R=next(p for p in Path(__file__).resolve().parents if (p/'bootloops-lean').is_file());H=R/'research/rmaf/algorithm/verification/output-state-2026-10-15';V=H/'review-v1';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
prior=[('pair-case-2026-10-15/frozen-review-v2',196,'59aaecf285bdbf2b1a98c869e21c32e35c191bd0140f055f32f7e497914cb8a2'),('rank-restriction-2026-10-15/frozen-ready-v1',32,'b27e9a0401a36be36c05ba119acbad0055c9d56593aab868a70662f82472ab0e'),('rank-restriction-2026-10-15/frozen-review-v1',372,'615411115f301b02da3fa082036048c6c95487d0ebc26d79faacbfa4adf9c685'),('depth-one-2026-10-15/frozen-ready-v1',46,'bcff1ad2931ec9991cb5de7c09bf8afa44253484602e38aec95e6d508e3fb787'),('depth-one-2026-10-15/frozen-review-v1',154,'efd0d5bbe74e4fa8b7e5b12b542b15412a86c4b116df4deec00a1529da24bd4f'),('output-state-2026-10-15/frozen-ready-v1',51,'0eb0bedc3a61d6645bdd2b3fd473f8fb659b8462f668e868c7ab288e80d34283')]
checks=[]
for rel,count,pin in prior:
 p=R/'research/rmaf/algorithm/verification'/rel/'MANIFEST.json';assert sha(p)==pin;d=json.loads(p.read_text());assert len(d['files'])==count
 for name,wanted in d['files'].items():assert sha(p.parent/name)==wanted,(rel,name)
 checks.append({'manifest':str(p.relative_to(R)),'sha256':pin,'matched':count})
M=R/'research/rmaf/algorithm/universal233/output_state/OUTPUT-STATE-MANIFEST-v1.json';assert sha(M)=='d27ae69ef54c6c03f20c43767fc0b731e5ff96abcfa59f1f426223c77e6a67f5';author=json.loads(M.read_text());assert len(author['immutable_files'])==313
for row in author['immutable_files']:assert sha(R/row['path'])==row['sha256'],row['path']
b=json.loads((R/'research/rmaf/results/algorithm-output-state-fresh-build-v1.json').read_text());assert len(b['source_copies'])==len(b['runs'])==121
for row in b['source_copies']:assert sha(R/row['path'])==row['sha256'] and sha(R/row['isolated'])==row['adapted_sha256']
audit=json.loads((R/'research/rmaf/results/algorithm-output-state-fresh-origin-audit-v4.json').read_text());assert audit['module_count']==124 and audit['declaration_count']==3898
for row in audit['declarations']:
 assert not row['rejected'] and not row['is_axiom'] and not row['unsafe']
 if row['kind'] in ['theorem','definition','opaque']:assert row['body_structural_hash64']!='none',row['name']
state_slice=(V/'isolated-source-v1/GroupState.lean').read_text().splitlines(keepends=True)[6:31];assert ''.join(state_slice)==(H/'frozen-ready-v1/frozen-inputs-v1/State-definitions-lines7-31.txt').read_text()
patterns=[r'\b(?:groundbreaking|revolutionary|unprecedented|game-changing)\b',r'\b(?:obviously|clearly trivial)\b'];prose=[]
for name in ['SEMANTIC-REVIEW-v1.md','RUNTIME-REVIEW-v1.md','CONSUMER-TRACE-v2.md','CONTACTS-AND-CORRECTIONS-v1.md']:
 text=(V/name).read_text();hits=[p for p in patterns if re.search(p,text,re.I)];assert not hits;assert 'OPEN' in text or name=='RUNTIME-REVIEW-v1.md';prose.append({'file':name,'pattern_pass':True,'second_manual_pass':'checked quantified scope, counts/denominators, actual-vs-abstract fixtures, assumed solver contract, source-vs-instruction runtime, retained failures and reserved external pass'})
(V/'SELF-EDITORIAL-CHECK-v1.json').write_text(json.dumps({'self_editing_only':True,'fresh_context_referee_credit':False,'passes':prose,'external_fresh_context_pass':'RESERVED_FOR_ROOT_AFTER_SEAL'},indent=2)+'\n')
result={'verdict':'PASS_FINAL_SOURCE_AND_SEAL_INTEGRITY','prior_ready_review_entries_matched':851,'prior_seals':checks,'author_manifest_sha256':sha(M),'author_entries_matched':313,'producer_and_isolated_source_pairs_matched':121,'successful_all_origin_modules':124,'successful_all_origin_declarations':3898,'every_value_bearing_theorem_definition_opaque_has_body_diagnostic':True,'permitted_State_definition_slice_byte_identical':True,'candidate_source_edits':0,'all_main_milestones':'OPEN'}
(R/'research/rmaf/results/algorithm-output-state-fresh-final-integrity-v2.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['verdict','prior_ready_review_entries_matched','author_entries_matched','producer_and_isolated_source_pairs_matched','successful_all_origin_declarations']}))
