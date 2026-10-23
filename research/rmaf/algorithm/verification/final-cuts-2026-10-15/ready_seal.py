"""One-shot immutable readiness seal; metadata/hash checks only, no author contact."""
from pathlib import Path
import json,hashlib,datetime
b=Path(__file__).resolve().parent;root=b.parents[4];h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
f=json.loads((b/'PRE-CANDIDATE-FREEZE.json').read_text())
assert h(b/'PRE-CANDIDATE-FREEZE.json')=='dd2339a7ab404db4bc3b15b1ccc3e00fc0846e757c93599c4d7703046bd2226b'
for path,sha in f['file_hashes'].items():assert h(root/path)==sha,path
assert h(b/'run_std_toys.py')==json.loads((b/'STD-RUNNER-PIN.json').read_text())['source_sha256']
fixed=json.loads((root/'research/rmaf/results/algorithm-final-cuts-fresh-review-fixed-v1.json').read_text());assert fixed['clean']==46 and fixed['plants_caught']==221
mass=json.loads((b/'MASS-CONTROL-RECEIPT.json').read_text());assert (mass['clean'],mass['wrong_cost_claims_caught'],mass['duplicate_mass_claims_caught'])==(12,12,12)
std=json.loads((b/'STD-TOY-RECEIPT.json').read_text());assert std['origin_counts']=={'CutClean':33,'CutUsed':3,'CutUnused':2}
assert sum(x['explicit_false_diagnostic'] for x in std['builds'])==2
oldpins={
 'actual-query-classifier-2026-10-15':'b7c7fa96d1ea95f91d41218e537b098ce15d5a9cee87375ec212a7f54837cdd8',
 'whole-source-work-2026-10-15':'2526f8cb77fad799770557765a9d862d54e84fd31a0c1d49e20afd4254741580',
 'core-work-2026-10-15':'61e9aaa274f9ac625939efc3315bf9aa93638435daa90ae039d41a5ebbc67455',
 'integration-2026-10-15':'4cbbba186a546ac48e5f27736b7a537a5d83d3b0bec40a2156b15d80040b1c65',
 'geometry-2026-10-15':'b18691927138dc6142fb4306aab87e096a8c3c5a5b9d305905f993cd65d075b6',
 'continuation-2026-10-15':'9e6ab630ae7332dd0d572e775f8ee75537c05d013476cc64add4cd9f6111c2b7'}
old=[]
for name,sha in oldpins.items():
 p=b.parent/name/'ARTIFACTS.json';assert h(p)==sha,(name,h(p));d=json.loads(p.read_text());fs=d.get('file_hashes',d.get('files',{}))
 if isinstance(fs,list):fs={x['path']:x['sha256'] for x in fs}
 for path,value in fs.items():assert h(root/path)==(value['sha256'] if isinstance(value,dict) else value),path
 old.append({'review':name,'entries_rechecked':len(fs),'manifest_sha256':sha})
readyprior=b.parent/'actual-query-classifier-2026-10-15/READY-ARTIFACTS.json';assert h(readyprior)=='655f32eef6ee281e4d820e49e26d2b20bbf694f11e27cb0605ca4c5d2ac5f535';assert len(json.loads(readyprior.read_text())['file_hashes'])==60
receipt={'status':'READY-INDEPENDENT-INSTRUMENTS-ONLY','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pre_execution_freeze_sha256':h(b/'PRE-CANDIDATE-FREEZE.json'),'clean_controls':46,'corrupt_twins_caught':221,'fixed_seconds':fixed['elapsed_seconds'],'supplemental_mass_clean':12,'wrong_cost_mass_caught':12,'duplicate_mass_caught':12,'Std_clean_origins':33,'Std_used_private_axon_origins':3,'Std_unused_private_axiom_origins':2,'Std_explicit_false_diagnostics':2,'Std_broken_import':'EXCLUDED-falsity','Std_detector_gates':std['controls'],'candidate_content_contact':False,'scientific_candidate_builds':0,'candidate_manifest_contact':False,'author_children_contact':False,'lineage_extra_replications':0,'all_three_main_milestones':'OPEN','main_necessity':'Once-only exact original cuts from selected final AF; no minimum forest selection or global recurrence certified','prior_reviews_rechecked':old,'prior_ready_entries_rechecked':60,'pre_freeze_correction':'CONTROL-DRAFT-v0 manual swapped-sibling block-inspection9→7 before any engine run; active prefreeze expectations unchanged after execution','current_execution_failures':'No pilot/fixed/toy detector failure; two expected explicit false and expected broken-import diagnostics. All preceding phases failures preserved.','later_review':'Separate exact root release required; fresh-context prose/referee pass reserved for later final sealed review, no self-credit'}
(b/'PRE-CANDIDATE-RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
contacts=json.loads((b/'SOURCE-CONTACTS.json').read_text());lineage='\n'.join('- '+x['path']+' SHA '+x['sha256'] for x in contacts['same_lineage_reuse'])
text=f'''# READY for separate exact final-cut release

Independent preparation is complete. The46 literal clean cases and221 corrupt twins passed. Supplemental exact raw-mass checks passed12 clean cases and rejected12 wrong-cost plus12 duplicate-mass claims. The original mass table and46/221 expectations were frozen before the first pilot; the supplemental detector source/false claims were pinned before its own execution. PRE-CANDIDATE-FREEZE SHA{h(b/'PRE-CANDIDATE-FREEZE.json')}.

The measured3-case pilot took0.006110500002250774s;4-case size pilot0.01618558399786707s; fixed46-case bank{fixed['elapsed_seconds']}s. PILOT-PROJECTION.json records the slowest measured-case projection. These timings describe only the local reference controls. Std-only Clean pilot0.34180866700262413s; the full origin audit took4.356677458999911s. No scientific candidate was compiled.

The graph instrument retains every original vertex, both removed-edge orientations, all components including leafless residues, roots, leaf multisets and cost/component equalities. It accepts9 explicitly valid alternate histories, with no invented unique original-cut tie. It catches root/nonedge/duplicate/missing cuts, dropped root/path/leafless components, class/empty-head/multiplicity errors, unsupported target transport and local-prototype/whole-original-edge conflation. Source-valid and crossed-target agreement are separate. The final work/mass checks count recovery only once after selection and reject hiding8 repeated recoveries as one. No source-cost/fine-instruction claim about the barred candidate is made.

Std-only tests enumerate33 clean module-origin declarations including private/generated structure names and accept the clean source; used and UNUSED private custom axioms are rejected. Missing/duplicate/wrong-origin records and source-byte/pin corruptions reject. Two false propositions have explicit decide-is-false diagnostics. Broken import is excluded from falsity. KERNEL-GATES.json specifies the full scientific-origin/import/body/adoption/kernel detector plan after separate release.

Same GPT-6.1 Sol xhigh reviewer/checker lineage, zero additional replications. Reused permitted inputs:

{lineage}

The earlier275 final review,60 readiness and237/192/203/69/42 freezes all recheck without edits. Root TARGET-v1 was read first and a skeleton written immediately. Author final_cut_recovery proofs, controls, receipts, auditor and manifest remain uncontacted; the618 count is administrative metadata only. No live forbidden main/outputstate/allgood/groups/binary/state/cherry/depth or other-reviewer code was read. No author or child contact.

All three main milestones remain OPEN. This READY establishes instruments only, not final recovery acceptance, a minimum-forest selector, a complete solver or a global recurrence. Await root's separate exact freeze release. The later separately assigned fresh-context prose/referee review is not credited here.
'''
(b/'READY.md').write_text(text)
(b/'WORKFILE-CURRENT.md').write_text('# Current preparation status\n\nREADY; see READY.md and PRE-CANDIDATE-RECEIPT.json. WORKFILE.md is the immutable initial skeleton pinned before execution.46/221 controls,12/12/12 supplemental mass and Std-only origin/false/axiom gates passed. No candidate content/builds; separate root release required. All3 OPEN; same lineage0 extra replications. No author/child contact.\n')
files={}
for p in sorted(b.rglob('*')):
 if p.is_file() and p.name!='READY-ARTIFACTS.json' and '__pycache__' not in p.parts and p.suffix not in ['.olean','.ilean','.o','.c'] and '.olean' not in p.name:files[str(p.relative_to(root))]=h(p)
for p in sorted((root/'research/rmaf/results').glob('algorithm-final-cuts-fresh-review-*')):
 if p.is_file():files[str(p.relative_to(root))]=h(p)
out={'status':'FROZEN-PRE-CANDIDATE-READY','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file_count':len(files),'file_hashes':files,'pre_execution_freeze_sha256':h(b/'PRE-CANDIDATE-FREEZE.json'),'candidate_contact':False,'candidate_builds':0,'additional_replications':0,'all_three_main_milestones':'OPEN','excludes':['compiled Std toy caches','Python caches','this manifest self-hash'],'later_review_writes':'new phase files only; every listed readiness file immutable'}
p=b/'READY-ARTIFACTS.json';p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'entries':len(files),'READY_ARTIFACTS_sha256':h(p),'READY_sha256':h(b/'READY.md'),'pre_execution_sha256':h(b/'PRE-CANDIDATE-FREEZE.json')}))
