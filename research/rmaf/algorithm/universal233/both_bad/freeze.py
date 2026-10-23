"""Freeze completed actual binary consumer; mutable logs/pointers excluded."""
from pathlib import Path
import hashlib,json,datetime
D=Path(__file__).resolve().parent;R=D.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
canonical=R/'results/algorithm-universal233-both-bad-20261015T115125Z'
record=json.loads((canonical/'certificate.json').read_text())
assert record['status']=='PASS_AUTHOR_SOURCE_BOUND_REPLAY'
skip={'LATEST-REPLAY.txt','Inspect.lean','replay.log','replay-final.log','BOTH-BAD-MANIFEST-v1.json','freeze.log'}
files=[p for p in D.iterdir() if p.is_file() and p.name not in skip]
files+=list(p for p in canonical.iterdir() if p.is_file())
old=R/'results/algorithm-universal233-both-bad-20261015T114836Z'
files += [old/'certificate.json',old/'ModuleAudit.log',old/'RESULT-input-at-first-run.md']
files += [R/'research/rmaf/results/algorithm-universal233-both-bad-v1.json']
obj={'version':1,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'scope':'actual both-bad original binary planner/dispatcher: universal original refinement coverage, conditional no-larger exactness, any-oracle actual callback mass<=4*c^-4 for2<=c<=3, childbudget+3<=q; full-prefix bill bounded; source cost qualification explicit',
 'status':'AUTHOR_SCOPED_MATH_COMPLETE_SOURCE_COST_QUALIFIED_REVIEW_PENDING',
 'all_three_main_milestones':'OPEN','complete_algorithm':False,'independent_acceptance':False,
 'canonical_receipt':str((canonical/'certificate.json').relative_to(R)),
 'source_modules':record['positive_source_modules'],'module_origins':record['module_origin_declarations'],
 'standard_axioms':record['standard_axioms_observed'],'false_claims_rejected':13,
 'excluded_mutable_development':sorted(skip|{'build/','__pycache__/'}),
 'no_write_boundary':'No further author writes to the listed payload; later corrections are appended outside this immutable set.',
 'immutable_files':[{'path':str(p.relative_to(R)),'sha256':sha(p)} for p in sorted(set(files))]}
p=D/'BOTH-BAD-MANIFEST-v1.json';p.write_text(json.dumps(obj,indent=2)+'\n')
for e in obj['immutable_files']:assert sha(R/e['path'])==e['sha256'],e['path']
print('FINAL FROZEN',len(obj['immutable_files']),'immutable payload files; manifest SHA',sha(p))
