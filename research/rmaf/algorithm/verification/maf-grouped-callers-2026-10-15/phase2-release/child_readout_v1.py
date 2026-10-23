"""Frozen four-label residual table against actual released ForestState.agrees.

This executes finite checker controls, not a residual solver implementation.
"""
from pathlib import Path
import importlib.util,json,sys
sys.dont_write_bytecode=True
import rebuild as R
spec=importlib.util.spec_from_file_location('own_frozen_child_model',R.HERE.parent/'instrument.py')
I=importlib.util.module_from_spec(spec);spec.loader.exec_module(I)
E=json.loads((R.HERE.parent/'EXPECTATIONS-v1.json').read_text())['child']
prior=R.ROOT/'research/rmaf/results/algorithm-maf-grouped-prerelease-addendum-v2.json'
frozen=json.loads(prior.read_text())
def lit(v):return '['+', '.join(lit(x) for x in v)+']' if isinstance(v,list) else str(v)
def tree(v):return f'(Tree.leaf {v})' if type(v) is int else f'(Tree.node {tree(v[0])} {tree(v[1])})'
def main():
    candidates=I.partitions(I.leaves(E['target']));assert len(candidates)==frozen['child_partition_count']==15
    text='''import FreshConsumer
import Lean
open RMAF Lean ForestState ForestGroups
namespace NonauthorChildControls
def target : Option Tree := some TARGET
def sources : List Tree := SOURCES
def candidates : List (List (List Nat)) := CANDIDATES
#eval IO.println ("TABLE|" ++ (toJson (candidates.map (fun F =>
  (agrees target sources F,additionalCost sources F)))).compress)
theorem constant_none_cannot_supply_child_contract :
    ¬ ResidualSolverContract (fun _ _ _ => none) target sources 1 := by
  intro IH
  have impossible := (IH (by decide)).1.1 rfl [[3],[5],[4,6]] (by decide)
  have cost : additionalCost sources [[3],[5],[4,6]]=1 := by decide
  omega
end NonauthorChildControls
'''.replace('TARGET',tree(E['target'])).replace('SOURCES','['+', '.join(tree(v) for v in E['sources'])+']').replace('CANDIDATES',lit(candidates))
    b=R.HERE/'isolated-groups';(b/'FreshChild.lean').write_text(text)
    build=R.helper().run(b,'FreshChild',['-o','FreshChild.olean']);assert build['exit']==0,build
    lines=[s.split('|',1)[1] for s in (b/'FreshChild.log').read_text().splitlines() if s.startswith('TABLE|')]
    assert len(lines)==1;actual=json.loads(lines[0]);assert len(actual)==15
    rows=[]
    for F,(ag,cost) in zip(candidates,actual,strict=True):
        expected=[I.state_agrees(E['target'],E['sources'],F),max(0,len(F)-len(E['sources']))]
        assert [ag,cost]==expected,(F,ag,cost,expected)
        rows.append({'forest':F,'actual_agrees':ag,'actual_cost':cost,'same_as_frozen_model':True})
    assert min(x['actual_cost'] for x in rows if x['actual_agrees'])==frozen['child_finite_minimum']==1
    contracts=[]
    for r in frozen['child_contract_rows']:
        budget=r['child_budget'];F=r['returned']
        feasible=any(x['actual_agrees'] and x['actual_cost']<=budget for x in rows)
        assert feasible==r['exists_valid_forest']==(F is not None)
        if F is not None:
            actual_return=next(x for x in rows if x['forest']==F)
            assert actual_return['actual_agrees'] and actual_return['actual_cost']<=budget
        contracts.append({'child_budget':budget,'actual_checker_feasible':feasible,'unchanged_frozen_return':F,'finite_feasibility_table_matches':True})
    out={'status':'PASS_ACTUAL_CHECKER_FROZEN_FINITE_CHILD_TABLE','build':build,'source_sha256':R.sha(b/'FreshChild.lean'),'frozen_addendum':str(prior.relative_to(R.ROOT)),'frozen_addendum_sha256':R.sha(prior),'partitions':15,'rows':rows,'contract_rows':contracts,'constant_none_contract_rejected_by_positive_theorem':True,'interpretation':'Actual checker finite controls only; no general residual solver, minimum-attainment IH or recursive termination constructed. The exact source contract remains supplied.','all_main_milestones':'OPEN','replication_count_added':0}
    dest=R.ROOT/'research/rmaf/results/algorithm-maf-grouped-fresh-review-child-readout-v1.json';dest.write_text(json.dumps(out,indent=2)+'\n');print(out['status'],len(rows),len(contracts))
if __name__=='__main__':main()
