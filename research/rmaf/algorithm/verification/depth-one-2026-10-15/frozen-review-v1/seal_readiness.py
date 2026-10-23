#!/usr/bin/env python3
"""One-shot metadata readiness seal; no candidate release or inspection."""
from pathlib import Path
import json,hashlib,shutil,datetime
H=Path(__file__).resolve().parent;ROOT=next(p for p in H.parents if (p/'bootloops-python').is_file());R=ROOT/'research/rmaf/results'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
p=json.loads((R/'algorithm-depth-one-fresh-pilot-v1.json').read_text());b=json.loads((R/'algorithm-depth-one-fresh-battery-v1.json').read_text());s=json.loads((R/'algorithm-depth-one-fresh-std-gates-v1.json').read_text())
assert p['verdict']==b['verdict']=='PASS-FROZEN-BLIND-DEPTH-ONE-CONTROLS'
assert p['literal_checks']==95 and b['literal_checks']==196 and b['mismatches_rejected']==196
assert b['original_edges_tested']==48 and b['one_two_partitions_tested']==61 and b['all_partitions_tested']==106
assert s['verdict']=='PASS-BLIND-STD-TOY-FALSE-CUSTOM-PRIVATE-IMPORT-AND-INVENTORY-GATES'
assert s['audits']['CleanAudit']['total']==19 and s['audits']['DirtyAudit']['total']==7 and s['audits']['DirtyAudit']['rejected_count']==6
assert len(s['metadata_mutations'])==5 and s['wrong_path_mutation_rejected'] and s['source_pin_corruption_rejected']
old=[]
for path,want,count in [('research/rmaf/algorithm/verification/rank-restriction-2026-10-15/frozen-review-v1','615411115f301b02da3fa082036048c6c95487d0ebc26d79faacbfa4adf9c685',372),('research/rmaf/algorithm/verification/rank-restriction-2026-10-15/frozen-ready-v1','b27e9a0401a36be36c05ba119acbad0055c9d56593aab868a70662f82472ab0e',32),('research/rmaf/algorithm/verification/pair-case-2026-10-15/frozen-review-v2','59aaecf285bdbf2b1a98c869e21c32e35c191bd0140f055f32f7e497914cb8a2',196)]:
 d=ROOT/path;mp=d/'MANIFEST.json';assert sha(mp)==want;m=json.loads(mp.read_text());assert len(m['files'])==count
 for f,h in m['files'].items():assert sha(d/f)==h
 old.append({'manifest':str(mp.relative_to(ROOT)),'sha256':want,'entries_rechecked':count})
control=H/'frozen-controls-v1';cm=json.loads((control/'MANIFEST.json').read_text())
for n,w in cm['files'].items():assert sha(control/n)==w
for row in cm['dependencies']:assert sha(ROOT/row['path'])==row['sha256']
summary={'status':'READY','phase':'PRE-CANDIDATE','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'candidate_contacts':0,'candidate_Lean_compilations':0,'original_scientific_Lean_compilations_this_phase':0,'Std_toy_gates_executed':True,'author_contacts':0,'children':0,'extra_independent_replications':0,'lineage':'Own prior original-address graph/checker reused; edge/partition routes share graph/topology layer; Lean origin API shared validation layer',
 'fixed_input_pairs':13,'proper_fixtures':10,'refused_fixtures':3,'literal_checks':196,'mismatched_expectation_mutations_rejected':196,'original_source_edges':48,'one_two_block_partitions':61,'full_partitions':106,'maximum_labels':4,'maximum_partition_denominator':15,'planted_checks_before_fixture_measurements':b['planted_checks_before_fixtures'],'pilot_literal_checks':95,'pilot_seconds':p['seconds'],'battery_seconds':b['seconds'],
 'Std_toys':{'clean_declarations':19,'dirty_client_declarations':7,'bad_declarations_rejected':6,'custom_axioms':3,'metadata_mutation_records':s['metadata_mutations'],'explicit_false_rejected':True,'private_and_generated_names_included':True,'actual_compiler':s['compiler']},'prior_seals_preserved':old,'failure_or_pin_erratum':None,'unsupported_or_timeouts':0,
 'candidate_claims':'UNREVIEWED; await separate exact final317 release','Algorithm':'OPEN','Correctness':'OPEN','Smaller_base':'OPEN','runtime_scope':'No candidate runtime source or cost contract inspected; no polynomial or fine-instruction claim accepted','novelty':'NOT_CLAIMED'}
(R/'algorithm-depth-one-fresh-ready-v1.json').write_text(json.dumps(summary,indent=2)+'\n')
D=H/'frozen-ready-v1';assert not D.exists();D.mkdir()
for p in H.iterdir():
 if p.is_file():shutil.copy2(p,D/p.name)
shutil.copytree(control,D/'frozen-controls-v1')
for p in (H/'isolated-std-v1').iterdir():
 if p.is_file() and p.suffix not in ['.olean','.ilean']:
  q=D/'isolated-std-v1'/p.name;q.parent.mkdir(exist_ok=True);shutil.copy2(p,q)
(D/'results').mkdir()
for p in sorted(R.glob('algorithm-depth-one-fresh-*-v1.json')):shutil.copy2(p,D/'results'/p.name)
files={str(p.relative_to(D)):sha(p) for p in sorted(D.rglob('*')) if p.is_file()};m={'phase':'PRE-CANDIDATE','status':'READY','file_count':len(files),'files':files,'prior_seals_preserved':old,'dependencies':cm['dependencies'],'candidate_contacts':0,'all_main_milestones':'OPEN'}
(D/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
for f,w in files.items():assert sha(D/f)==w
seal={'manifest':str((D/'MANIFEST.json').relative_to(ROOT)),'sha256':sha(D/'MANIFEST.json'),'entries':len(files),'status':'READY','candidate_contacts':0,'summary_sha256':sha(R/'algorithm-depth-one-fresh-ready-v1.json')}
(H/'READY-SEAL-v1.json').write_text(json.dumps(seal,indent=2)+'\n')
for p in D.rglob('*'):p.chmod(p.stat().st_mode & ~0o222)
D.chmod(D.stat().st_mode & ~0o222);print(json.dumps(seal))
try:
 from telemetry import artifact,metric,gate
 artifact(str(D/'MANIFEST.json'));artifact(str(R/'algorithm-depth-one-fresh-ready-v1.json'));metric('blind literal controls',196,total=196,unit='checks');gate('known_truth','passed',detail='PRE-CANDIDATE readiness only; depth_one unreviewed, all three main milestones OPEN')
except ImportError:pass
