#!/usr/bin/env python3
"""One-shot final acceptance assembly; hash and diagnostic gates must all pass."""
import hashlib,json,os
from pathlib import Path
HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(name):return json.loads((HERE/name).read_text())
manifest=read('source-manifest.json')
for row in manifest:assert sha(Path(row['source']))==row['sha256']==sha(Path(row['snapshot']))
report=HERE.parent/'REPORT.md'; trace=HERE.parent/'USE-SITE-TRACE.md'
assert sha(report)=='9ef1c407cb5f32588dfd34814a44dc855ff1e6323f3f08998bbe9c0860b0aa5f'
assert sha(trace)=='ac3c9013f25fd4d1d03121b8b3b74137e3bd968a86d9ae5d606cd09ab4b01b6c'
assert report.read_bytes()==(HERE/'REPORT-reviewed.md').read_bytes()
assert trace.read_bytes()==(HERE/'USE-SITE-TRACE-reviewed.md').read_bytes()
audit=read('source-audit.json');assert audit['status']=='PASS'
for row in audit['false_rejections']:
 log=(HERE/(row['name']+'.log')).read_text()
 assert log.count(': error:')==1 and 'Tactic `decide` proved that the proposition' in log and 'is false' in log
 assert not any(s in log for s in ('Type mismatch','Unknown identifier','failed to synthesize','unsolved goals'))
assert 'sorryAx' not in (HERE/'ReviewerChecks.log').read_text()
for name in ('build-pilot.json','build-main.json','build-review.json'):
 for row in read(name):
  assert row['returncode']==0
  assert row['source_sha256']==sha(HERE/'build'/(row['module']+'.lean'))
panel=read('source-panel-5.json')
assert panel['returncode']==0 and panel['cases']==3850 and panel['equalities']==7700 and panel['zero_axiom_reports']==3850
assert panel['source_sha256']==sha(HERE/'build/FiniteSourcePanel5.lean')
def item(i,label,status,detail):return dict(id=i,label=label,status=status,detail=detail)
result=dict(
 status='CONFIRMED_SCOPED_TARGET',
 scope='Exact-source actual MinimalEmbedding constructor with actual ambient/selected-occurrence semantics, terminal preservation, universal leastness, exact original region and compiled original consumer.',
 candidate_authorship='None; reviewer authored only fresh_review artifacts.',
 source_hashes={r['source']:r['sha256'] for r in manifest},
 main_report_sha256=sha(report),use_site_trace_sha256=sha(trace),review_report_sha256=sha(HERE/'REVIEW.md'),
 frozen_spec_sha256=sha(HERE/'FROZEN-SPEC.md'),
 metrics={
  'controls':item('controls','Literal fixtures and corruptions','passed','11 fixtures and 6 corruptions with passing twins'),
  'graph_oracle':item('graph-oracle','Independent LCA/intersection comparison','passed_finite','3850 cases: 2681 nonempty selections and 1169 null cases; 16373 feasible connected supports'),
  'source_panel':item('source-panel','Exact finite source comparison','passed_finite','3850 theorems, 7700 support/terminal equalities, 3850 empty axiom reports'),
  'build':item('final-source-build','Fresh dependency/interface build','passed','7 exact source modules rebuilt in isolated LEAN_PATH, plus reviewer field and original consumer tests'),
  'axioms':item('axiom-inventory','Whole-chain axiom inventory','passed','148 theorem/definition/abbreviation reports; only propext, Classical.choice, Quot.sound or none; not an aggregate theorem count'),
  'false_controls':item('false-controls','Exact false diagnostics','passed','6 explicit-false failures, each with exactly one intended error; malformed True proof excluded and clean twin passed'),
  'report':item('report-review','Fresh prose/referee review','passed_after_corrections','Final leaf-label functionality wording, Tree type notation and qualified theorem name checked; exact final report/trace snapshots pinned')},
 lemmas=[
  item('occurrence-semantics','Actual vertex and selected occurrence interpretation','confirmed','Membership iff inductive valid/leaf occurrences; functionality unconditional and address uniqueness conditional on Nodup'),
  item('actual-constructor','Actual MinimalEmbedding from unchanged extractor','confirmed','Every original structure field derived from tree, selection and occurring-selected-label witness'),
  item('leastness','Universal leastness','confirmed','Every connected terminal-containing support includes extractor output; no target property is a theorem premise'),
  item('original-consumer','Exact original region and consumer composition','confirmed','Original MinimalEmbedding interface compiled with explicit depth/coordinate-overlap assumptions'),
  item('independent-lca','Independent LCA-prefix derivation','ordinary_derivation_with_finite_checks','Frozen before candidate source inspection; separate from the universal candidate Lean proof')],
 checks_not_run=['project-wide bootloops-check','separate new universal Lean proof of independent LCA hull formulation'],
 not_established=['cross-tree restriction/suppression transport','G2-G7','exchange realization','safe cover','faster or unrestricted runtime bound','novelty'],
 retained_failed_attempts=['ReviewerChecks-attempt1.lean','ReviewerChecks-attempt1.log','audit_sources-attempt1.py','audit_sources-attempt1.log'],
 records={name:sha(HERE/name) for name in ('source-manifest.json','source-audit.json','build-pilot.json','build-main.json','build-review.json','lca-check-5.json','source-panel-5.json','referee_sim_REPORT.md','build/ReviewerChecks.lean','independent_lca_check.py','source_panel.py','rebuild.py','audit_sources.py')})
tmp=HERE/'acceptance.json.tmp';tmp.write_text(json.dumps(result,indent=2)+'\n');os.replace(tmp,HERE/'acceptance.json')
print(json.dumps(dict(status=result['status'],receipt=str(HERE/'acceptance.json'),sha256=sha(HERE/'acceptance.json'),review_report_sha256=result['review_report_sha256'])))
