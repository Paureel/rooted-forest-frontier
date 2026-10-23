#!/usr/bin/env python3
"""One-shot local prerelease readiness snapshot and metadata aggregation."""
import json,hashlib,shutil
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=next(p for p in (HERE,*HERE.parents) if (p/'bootloops-python').is_file())
RES=ROOT/'research/rmaf/results'
load=lambda n:json.loads((RES/('algorithm-rank-restriction-fresh-'+n+'-v1.json')).read_text())
b=load('battery');p=load('pilot');q=load('restriction-pilot');a=load('actual-clearing')
assert b['verdict']=='FROZEN-PRERELEASE-CONTROLS-PASSED' and b['literal_check_denominator']==171 and b['mismatches_rejected']==171
assert a['verdict']=='ACTUAL-OUTPUT-CLEARING-CONTROLS-PASSED' and a['literal_checks']==14
assert all(x['passed'] and x['mismatched_expectation_rejected'] for x in a['checks'])
old=ROOT/'research/rmaf/algorithm/verification/pair-case-2026-10-15/frozen-review-v2'
old_manifest=json.loads((old/'MANIFEST.json').read_text())
assert hashlib.sha256((old/'MANIFEST.json').read_bytes()).hexdigest()=='59aaecf285bdbf2b1a98c869e21c32e35c191bd0140f055f32f7e497914cb8a2'
for f,h in old_manifest['files'].items():assert hashlib.sha256((old/f).read_bytes()).hexdigest()==h
assert len(old_manifest['files'])==196
for path,h in [('research/rmaf/algorithm/universal233/core/CoreProgram.lean','9aa92355dfecf6e0e3d7707c1c284cabcb2f3846b6682e3b55b719e35cb7311f'),('research/rmaf/algorithm/universal233/core/CoreGraph.lean','7099d4aa48a771f1d56e11bd36447a51d7e3c57094a6779c0d40acec11dca7a0')]:
    assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==h
summary={'phase':'PRERELEASE','status':'READY','scope':'Controls/instruments only. Candidate rank/restriction proofs and actual cheap/high/SolveForest consumers unreviewed; all main milestones OPEN.',
 'lineage':{'same_reviewer_as_G_E':True,'own_frozen_graph_instrument_reused':True,'extra_independent_replications':0,'candidate_contact':False,'candidate_Lean_compilation':False,'original_Lean_execution_this_phase':False,'author_contacts':0,'children':0},
 'literal_checks':185,'mismatched_expectations_rejected':185,'pilot_repeated_literal_checks':p['literal_check_denominator']+q['literal_check_denominator'],
 'rank_cases':len(b['rank_cases']),'rank_enumerated_partitions':sum(x.get('partition_denominator',0) for x in b['rank_cases']),
 'proper_rank_budgets':sum(len(x.get('budgets',[])) for x in b['rank_cases']),
 'raw_rank_output_occurrences':sum(len(y['receipt']['outputs']) for x in b['rank_cases'] for y in x.get('budgets',[])),
 'exact_rational_mass_bounds':sum(len(x.get('mass_checks',[])) for x in b['rank_cases']),
 'restriction_cases':len(b['restriction_cases']),'forward_local_families':sum(len(x['families']) for x in b['restriction_cases']),
 'original_path_transports':sum(len(x['transports']) for x in b['restriction_cases']),
 'supplementary_actual_output_clearing_cases':2,'supplementary_raw_occurrences':4,'supplementary_Bell_partitions':0,
 'timing_seconds':{'rank_pilot':p['seconds'],'restriction_pilot':q['seconds'],'fixed_battery':b['seconds']},
 'future_Lean_gates':'LEAN-GATES-v1.json preregistered; execution awaits exact manifest release',
 'prior_G_E_review_preserved':{'manifest_sha256':'59aaecf285bdbf2b1a98c869e21c32e35c191bd0140f055f32f7e497914cb8a2','all196entries_rechecked':True},
 'claims':{'rank_universal_theorems':'UNREVIEWED','restriction_universal_theorems':'UNREVIEWED','actual_cheap_high_consumer':'OPEN-PENDING-RELEASE','actual_SolveForest_reconstruction_budget_consumer':'OPEN-PENDING-RELEASE','Algorithm':'OPEN','Correctness':'OPEN','Smaller_base':'OPEN'},
 'failure_or_pin_erratum':None,'no_query_cost_discount_assumed':True,'requested_clearing_not_promoted_to_Q_disjointness':True}
assert summary['rank_enumerated_partitions']==78 and summary['proper_rank_budgets']==44
assert summary['raw_rank_output_occurrences']==41 and summary['exact_rational_mass_bounds']==219
assert summary['forward_local_families']==15 and summary['original_path_transports']==100
(RES/'algorithm-rank-restriction-fresh-ready-v1.json').write_text(json.dumps(summary,indent=2)+'\n')
DEST=HERE/'frozen-ready-v1';assert not DEST.exists();DEST.mkdir()
for f in HERE.iterdir():
    if f.is_file() and (f.suffix in ('.py','.json','.jsonl','.md') or 'SHA256SUMS' in f.name):shutil.copy2(f,DEST/f.name)
shutil.copytree(HERE/'frozen-controls-v1',DEST/'frozen-controls-v1',ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
(DEST/'results').mkdir()
for f in RES.glob('algorithm-rank-restriction-fresh-*-v1.json'):shutil.copy2(f,DEST/'results'/f.name)
files={str(f.relative_to(DEST)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(DEST.rglob('*')) if f.is_file()}
manifest={'phase':'PRERELEASE','status':'READY','file_count':len(files),'files':files,'candidate_contact':False,'all_main_milestones':'OPEN'}
(DEST/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
for path,h in files.items():assert hashlib.sha256((DEST/path).read_bytes()).hexdigest()==h
seal=hashlib.sha256((DEST/'MANIFEST.json').read_bytes()).hexdigest()
(HERE/'READY-SEAL-v1.json').write_text(json.dumps({'manifest':str((DEST/'MANIFEST.json').relative_to(ROOT)),'sha256':seal,'entries':len(files)},indent=2)+'\n')
for f in DEST.rglob('*'):f.chmod(f.stat().st_mode & ~0o222)
DEST.chmod(DEST.stat().st_mode & ~0o222)
print(json.dumps({'status':'READY','manifest_sha256':seal,'entries':len(files),'literal_checks':185,'old_G_E_196_entries_unchanged':True}))
