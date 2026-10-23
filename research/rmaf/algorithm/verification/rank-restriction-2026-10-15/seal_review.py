#!/usr/bin/env python3
"""Seal scoped review, every failed/corrected instrument, and exact source provenance."""
from pathlib import Path
import json,hashlib,shutil,datetime
HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'bootloops-python').is_file());RES=ROOT/'research/rmaf/results'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def load(tag,version=1):return json.loads((RES/f'algorithm-rank-restriction-fresh-{tag}-v{version}.json').read_text())
def oldseal(folder,want,count):
 p=folder/'MANIFEST.json';assert sha(p)==want
 d=json.loads(p.read_text());assert len(d['files'])==count
 for f,h in d['files'].items():assert sha(folder/f)==h,(folder,f)
 return {'manifest':str(p.relative_to(ROOT)),'manifest_sha256':want,'files_rechecked':count}
prior=[oldseal(HERE/'frozen-ready-v1','b27e9a0401a36be36c05ba119acbad0055c9d56593aab868a70662f82472ab0e',32),oldseal(ROOT/'research/rmaf/algorithm/verification/pair-case-2026-10-15/frozen-review-v2','59aaecf285bdbf2b1a98c869e21c32e35c191bd0140f055f32f7e497914cb8a2',196)]
release=json.loads((HERE/'RELEASED-PINS-v1.json').read_text())
for kind,d in release.items():
 assert sha(ROOT/d['manifest'])==d['manifest_sha256']
 for row in d['matched_files']:assert sha(ROOT/row['path'])==row['sha256']
 assert sha(ROOT/d['receipt'])==d['receipt_sha256']
g=load('lean-gates');b=load('released-battery');c=load('released-actual-clearing');o=load('origin-adoption');s=load('signature-inventory',2);v=load('actual-definitions',2);f=load('interface-gates');j=load('joint-consumer',2);col=load('canonical-colors',2);cp=load('clearing-counterproofs')
assert g['verdict']=='OWN-PREREGISTERED-LEAN-GATES-PASSED-BEFORE-CANDIDATE-POSITIVES'
assert b['literal_check_denominator']==171 and b['mismatches_rejected']==171
assert c['literal_checks']==14 and all(x['passed'] and x['mismatched_expectation_rejected'] for x in c['checks'])
assert o['same_exact_declaration_names']==694 and len(o['origin_adoptions'])==13
assert s['exact_type_count']==694 and s['exact_body_count']==691 and len(s['generated_proof_body_differences'])==3
assert len(v['comparisons'])==861 and all(x['passed'] for x in v['comparisons'])
assert sum(x['rejected_false_claims'] for x in f['negative_controls'].values())==8
assert f['source_pin_control']['clean_sha256']=='fc3336d4dd996330f077cd7407d6e63796b332b625b374ccde34ef278c04d7aa'
assert j['verdict'].startswith('PASS-') and j['audits']['joint/FreshJointOriginAuditV2']['total']==2371
assert col['verdict'].startswith('PASS-') and len(col['comparisons'])==9
assert cp['verdict']=='PASS-TWO-KERNEL-CHECKED-ACTUAL-OUTPUT-CLEARING-COUNTEREXAMPLES'
assert all(x['verdict'].startswith('PASS-') for x in [o,s,v,f,j,col,cp])
initial=load('source-rebuild');assert len(initial['rank_order'])==51 and len(initial['restriction_order'])==12
assert initial['audits']['rank/FreshOriginAudit']['total']==2194 and initial['audits']['restriction/FreshOriginAudit']['total']==694
assert not initial['audits']['rank/FreshOriginAudit']['bad'] and not initial['audits']['restriction/FreshOriginAudit']['bad']
archive=json.loads((HERE/'LOSSLESS-EXPR-ARCHIVE-v1.json').read_text())
for row in archive['archives']:assert sha(ROOT/row['archive_path'])==row['archive_sha256'] and row['decompression_verified']
summary={'status':'SCOPED_NONAUTHOR_CONFIRMED','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'root_target_sha256':sha(HERE/'TARGET-v1.md'),
 'rank_universal_theorems':'NONAUTHOR-CONFIRMED within root TARGET-v1','restriction_universal_theorems':'NONAUTHOR-CONFIRMED within root TARGET-v1','own_guarded_actual_output_cost_interface':'LEAN-PROVED and all-origin audited',
 'live_cheap_high_classifier':'OPEN; barred implementation not inspected','live_SolveForest_restriction_reconstruction_budget':'OPEN; barred implementation not inspected; target-Q guard remains explicit',
 'Algorithm':'OPEN','Correctness':'OPEN','Smaller_base':'OPEN','novelty':'NOT_CLAIMED','extra_independent_replications':0,'lineage':'Same reviewer as G/E; own frozen graph instrument reused; Lean audit API shared validation layer','author_contacts':0,'children':0,
 'frozen_controls':{'literal_checks':185,'mismatched_expectation_mutations_rejected':185,'actual_definition_comparisons':861,'postrelease_request_color_readouts':9,'actual_counterexamples_kernel_proved':2,'false_candidate_propositions_rejected':8,'larger_fixture_Bell_partitions':0},
 'source_replay':{'rank_origins':51,'rank_declarations':2194,'rank_private_names':196,'restriction_origins':12,'restriction_declarations':694,'restriction_private_names':70,'joint_origins':60,'joint_declarations':2371,'permitted_axioms_only':['propext','Classical.choice','Quot.sound'],'actual_compiler':g['actual_compiler'],'candidate_source_edits':0,'author_runners_executed':0},
 'generated_origin_provenance':{'same_restriction_names':694,'same_exact_types':694,'same_exact_proof_definition_bodies':691,'attributed_origin_changes':13,'three_generated_proof_bodies':'Exact private-helper prefix substitution; both retained, no executable definition changed','details':'signature-inventory-v2 receipt and origin-adoption-v1 receipt'},
 'retained_failures':[{'receipt':'source-rebuild-v1','cause':'Strict per-origin count expected import-order invariance; both full audits clean; diagnosed 13 generated-origin adoptions','resolution':'origin-adoption-v1 and signature-inventory-v2'},{'receipt':'signature-inventory-v1.json.gz','cause':'Strict body identity fails on three generated equation proof helper prefixes','resolution':'All 694 types identical; 691 bodies identical; exact three prefix substitutions verified; original payload losslessly archived'},{'receipt':'actual-definitions-v1','cause':'Unknown control-local refines identifier','resolution':'Actual contained all/any Boolean, no changed expectation; v2 passed'},{'receipt':'joint-consumer-v1','cause':'Reserved local binder; failed error-recovery sorryAx received no acceptance','resolution':'Binder renamed; corrected v2 source and all-origin audit passed without sorryAx'},{'receipt':'canonical-colors-v1','cause':'Requests import and top-level VertexGeometry namespace omitted','resolution':'Explicit frozen import/namespace; v2 expectations unchanged and passed'},{'phase':'initial checksum command','cause':'Wrong cwd caused shasum released_replay.py to fail and create an empty owned root checksum file','resolution':'Correct own-directory checksum written; empty accidental file removed; no scientific source/result changed'}],
 'prior_immutable_reviews_rechecked':prior,'released_pins_rechecked':{'rank':193,'restriction_local_plus_dependencies':16},'full_expr_archives':archive['archives'],
 'acceptance_basis':'Fresh semantic rederivation plus exact source-only kernel replay and complete originating declaration/type/body/axiom audits; finite tests interpret definitions and refute stronger unguarded extension only',
 'unclosed_consumer_conditions':['Target-Q original embedding disjointness for any reverse caller','Actual live caller hypothesis derivations','Remaining-budget allocation and total recursive states','Termination and running time/source-machine correspondence','Complete faster MAF algorithm and global base']}
summarypath=RES/'algorithm-rank-restriction-fresh-review-v1.json';summarypath.write_text(json.dumps(summary,indent=2)+'\n')
timing={'source_compile_seconds':sum(x['seconds'] for x in initial['runs'] if x['module']!='FreshOriginAudit'),'source_origin_audit_seconds':sum(x['seconds'] for x in initial['runs'] if x['module']=='FreshOriginAudit'),'actual_readout_seconds':sum(x['seconds'] for x in v['runs']),'full_expr_export_seconds':sum(x['seconds'] for x in s['runs']),'lossless_archive_seconds':sum(x['seconds'] for x in archive['archives']),'unsupported_or_timeouts':0,'scope':'Measured bounded local work only; CPU and exit status are not scientific acceptance'}
(HERE/'TIMING-RELEASE-v1.json').write_text(json.dumps(timing,indent=2)+'\n')
DEST=HERE/'frozen-review-v1';assert not DEST.exists();DEST.mkdir()
# Current source/provenance roots plus all own isolated sources/logs; no oleans adopted.
for p in HERE.iterdir():
 if p.is_file():shutil.copy2(p,DEST/p.name)
for sub in ['isolated-release-v1']:
 for p in (HERE/sub).rglob('*'):
  if p.is_file() and p.suffix not in ['.olean','.ilean','.pyc']:
   q=DEST/p.relative_to(HERE);q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
(DEST/'results').mkdir()
for p in sorted(RES.glob('algorithm-rank-restriction-fresh-*')):
 if p.is_file():shutil.copy2(p,DEST/'results'/p.name)
files={str(p.relative_to(DEST)):sha(p) for p in sorted(DEST.rglob('*')) if p.is_file()}
manifest={'status':'SCOPED_NONAUTHOR_CONFIRMED','all_three_main_milestones':'OPEN','file_count':len(files),'files':files,'external_prior_pins':prior,'rank_manifest_sha256':release['rank']['manifest_sha256'],'restriction_manifest_sha256':release['restriction']['manifest_sha256'],'lossless_archives':'LOSSLESS-EXPR-ARCHIVE-v1.json; original payload hashes and decompression checks retained','replications_added':0}
mp=DEST/'MANIFEST.json';mp.write_text(json.dumps(manifest,indent=2)+'\n')
for f,h in files.items():assert sha(DEST/f)==h
seal={'manifest':str(mp.relative_to(ROOT)),'sha256':sha(mp),'entries':len(files),'summary':str(summarypath.relative_to(ROOT)),'summary_sha256':sha(summarypath),'status':'SCOPED_NONAUTHOR_CONFIRMED','all_three_main_milestones':'OPEN'}
(HERE/'REVIEW-SEAL-v1.json').write_text(json.dumps(seal,indent=2)+'\n')
for p in DEST.rglob('*'):p.chmod(p.stat().st_mode & ~0o222)
DEST.chmod(DEST.stat().st_mode & ~0o222)
print(json.dumps(seal))
try:
 from telemetry import artifact,metric,gate
 artifact(str(summarypath));artifact(str(mp));metric('frozen literal checks',185,total=185,unit='checks');metric('actual definition comparisons',861,total=861,unit='comparisons');gate('known_truth','passed',detail='Scoped rank/restriction and guarded seam only; live consumers and all three main algorithm milestones OPEN. '+str(summarypath))
except ImportError:pass
