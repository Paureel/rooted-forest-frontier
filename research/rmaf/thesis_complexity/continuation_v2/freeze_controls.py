"""Receipt extraction only: freezes exposed controls before X0/construction."""
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / 'research/rmaf'
HERE = Path(__file__).resolve().parent

def read(p):
    return json.loads((ROOT/p).read_text())

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

refs = {
    'old_catalog': 'research/rmaf/thesis_complexity/repair/controls-frozen.json',
    'nine': 'research/rmaf/results/thesis-complexity-reachable-trace.json',
    'thirteen': 'research/rmaf/results/thesis-complexity-three-credit-trace.json',
    'interface': 'research/rmaf/results/thesis-runtime-repair-fresh-review-interface.json',
    'inside': 'research/rmaf/results/thesis-runtime-repair-fresh-review-history-final.json',
    'inside_replay': 'research/rmaf/results/thesis-runtime-repair-fresh-review-history-replay.json',
    'inside_lean': 'research/rmaf/results/thesis-runtime-repair-fresh-review-history-lean.json',
    'prior_summary': 'research/rmaf/results/thesis-runtime-repair-summary.json',
    'prior_manifest': 'research/rmaf/thesis_complexity/repair/manifest.json',
}
d = {k: read(p) for k,p in refs.items()}
assert d['nine']['leaf_count_excluding_rho'] == 9
assert d['thirteen']['trace'][-1]['P_Q_cardinalities'] == [3,2]
assert d['inside']['metrics']['actual_C_count'] == 2
assert d['inside']['fire']['residual'] == 1
assert d['interface']['actual_negative_budget']['child_budget'] == -4
assert d['interface']['negative_formula_fire']['rhs'] == '-23/8'
controls = []
for item in d['old_catalog']['controls']:
    controls.append({**item, 'quality': 'certified-finite-control',
                     'provenance': refs['old_catalog'],
                     'scope': 'exposed inherited control, not held-out discovery or a universal theorem'})
controls += [
    {'id':'inside-b-reached', 'quality':'independently-reviewed-finite-witness',
     'provenance':refs['inside'], 'instance':d['inside']['fire']['instance'],
     'expected':{'inside_b':True,'C_invocations':2,'J_pendants':3,'J_e_active_roots':3,'P':['a'],'Q':[]},
     'scope':d['inside']['formal_limits']},
    {'id':'false-outside-b', 'quality':'planted-false-conclusion',
     'same_instance_as':'inside-b-reached','claim':'x is outside b',
     'expected_accepted':False,'lhs':1,'rhs':0,'residual':1},
    {'id':'actual-negative-budget', 'quality':'independently-reviewed-finite-witness',
     'provenance':refs['interface'], **d['interface']['actual_negative_budget']},
    {'id':'false-negative-exponential', 'quality':'planted-abstract-arithmetic-misuse',
     'provenance':refs['interface'], **d['interface']['negative_formula_fire'],
     'expected_accepted':False},
    {'id':'weak-consumer-composition', 'quality':'checked-conditional-arithmetic',
     'provenance':refs['interface'],
     'exact':next(r for r in d['interface']['compositions'] if r['X']=='128' and r['kind']=='weak-C')},
    {'id':'strong-consumer-composition', 'quality':'checked-conditional-arithmetic',
     'provenance':refs['interface'],
     'exact':next(r for r in d['interface']['compositions'] if r['X']=='128' and r['kind']=='strong-C')},
    {'id':'G4-original-mismatch', 'quality':'checked-conditional-arithmetic-failure',
     'provenance':refs['interface'],
     'exact':next(r for r in d['interface']['rows'] if r['id']=='G4.1-A3-hard-exception')},
]
out = {
    'schema_version':1, 'frozen_at':datetime.now(timezone.utc).isoformat(),
    'stage':'before separate X0 and all construction',
    'convention':'labelled unary rho; thesis cuts; full permitted call tree; physical protections distinct from analysis credits',
    'alpha_control':128,
    'alpha_scope':'calibration only; source supplies no fixed sufficient global constant',
    'controls':controls,
    'trace_data':{'nine':d['nine'],'thirteen':d['thirteen'],'inside_C_tree':d['inside']['actual_C']},
    'source_correspondence':d['inside']['source_correspondence'],
    'source_Q_ambiguity':'Thirteen-leaf Q={x,u} uses displayed p119 recurrence; prose adds the cut endpoint instead. New twelve-leaf history does not use this ambiguity.',
    'references':[{'key':k,'path':p,'sha256':digest(ROOT/p)} for k,p in refs.items()],
    'failure_conditions':['wrong exact fixture','accepted planted outside-b conclusion','negative terminal undercount','silent Q convention change','credit/protection conflation','unlicensed frontier allowance'],
}
target = HERE/'controls-frozen.json'
assert not target.exists(), 'never overwrite frozen controls'
target.write_text(json.dumps(out,indent=2)+'\n')
old_files = sorted(p for p in (BASE/'thesis_complexity/repair').rglob('*') if p.is_file())
old_files += sorted((BASE/'results').glob('thesis-runtime-repair-*'))
snapshot = {'scope':'prior repair files and repair result receipts, preserve unchanged',
            'files':[{'path':str(p.relative_to(ROOT)),'sha256':digest(p)} for p in old_files]}
(HERE/'prior-evidence-snapshot.json').write_text(json.dumps(snapshot,indent=2)+'\n')
p=BASE/'progress/thesis-runtime-continuation-v2.json'
progress=json.loads(p.read_text())
progress['metrics']['frozen_controls']=len(controls)
progress['metrics']['prior_files_hash_pinned']=len(old_files)
progress['summary']='Twelve exact controls frozen from retained receipts; separate X0 adversary is next. Universal C-prefix and credited A bounds remain open.'
progress['artifacts'] += [str(target.relative_to(ROOT)),str((HERE/'prior-evidence-snapshot.json').relative_to(ROOT))]
temp=p.with_suffix('.json.tmp');temp.write_text(json.dumps(progress,indent=2)+'\n');temp.replace(p)
receipt={'controls':len(controls),'sha256':digest(target),'prior_files_hash_pinned':len(old_files),'phase':'frozen-before-X0','scientific_status':'no new claim checked by extraction'}
(BASE/'results/thesis-runtime-continuation-v2-freeze.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
