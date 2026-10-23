"""Pre-candidate gate strengthening: opaque runtime metadata and child contract."""
from pathlib import Path
from collections.abc import Mapping
from fractions import Fraction
from datetime import datetime,timezone
import hashlib,json,sys,time
sys.dont_write_bytecode=True
import instrument as I
HERE=Path(__file__).resolve().parent;ROOT=I.ROOT
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class PublicCase(Mapping):
    allowed={'source','target','Q','q','slot_ids','witnesses','fail_slot'}
    def __init__(self,c):self.public={k:c[k] for k in self.allowed if k in c}
    def __getitem__(self,k):
        if k in ('local_minima','minimum','out_of_minimum_contract','correctness_witness'):
            raise RuntimeError('runtime read of unknown semantic metadata')
        return self.public[k]
    def __iter__(self):return iter(self.public)
    def __len__(self):return len(self.public)
def main():
    pin=json.loads((HERE/'ADDENDUM-FREEZE-v2.json').read_text())
    for r in pin['files']:assert sha(ROOT/r['path'])==r['sha256']
    E=json.loads((HERE/'EXPECTATIONS-v1.json').read_text());start=time.monotonic();checks=[]
    old=I.local_minimum
    def poison(*a):raise RuntimeError('runtime called unknown optimum oracle')
    I.local_minimum=poison
    for c in E['original_cases']:
        r=I.run_caller(PublicCase(c));assert r['trace']==c['expected_calls'] and r['forest']==c['expected_forest']
        checks.append({'id':c['id'],'only_public_runtime_fields':True,'unknown_optimum_function_available':False})
    I.local_minimum=old
    catches=[]
    for name,operation in [('unknown-minimum-field',lambda:PublicCase(E['original_cases'][0])['local_minima']),('correctness-witness-field',lambda:PublicCase(E['original_cases'][0])['correctness_witness'])]:
        caught=False
        try:operation()
        except RuntimeError:caught=True
        assert caught;catches.append({'id':name,'caught':True})
    child=E['child'];labels=I.leaves(child['target']);assert len(labels)==4
    candidates=I.partitions(labels);assert len(candidates)==15
    valid=[F for F in candidates if I.state_agrees(child['target'],child['sources'],F)]
    minimum=min(len(F)-len(child['sources']) for F in valid);assert minimum==1
    assert I.state_agrees(child['target'],child['sources'],[[3],[5],[4,6]])
    assert I.state_agrees(child['target'],child['sources'],[[3],[4],[5],[6]])
    contract={'target':child['target'],'sources':child['sources'],'kind':'ResidualFeasibility'}
    rows=[]
    for budget in (0,1,2):
        r=I.child_query(child,budget+1,contract);F=r['forest'];feasible=any(0<=len(f)-len(child['sources'])<=budget for f in valid)
        assert r['budget']==budget and (F is not None)==feasible
        if F is not None:assert I.state_agrees(child['target'],child['sources'],F) and 0<=len(F)-len(child['sources'])<=budget
        rows.append({'child_budget':budget,'exists_valid_forest':feasible,'returned':F,'sound_complete_for_this_finite_case':True})
    # A finite semantic comparator, with clean and corrupted tables, rejects
    # a supplied Boolean that contradicts actual feasibility/soundness.
    def table_valid(table):
        if [x['child_budget'] for x in table] != [0,1,2]:return False
        for row in table:
            b=row['child_budget'];F=row['returned']
            feasible=any(0<=len(f)-len(child['sources'])<=b for f in valid)
            if (F is not None)!=feasible:return False
            if F is not None and (not I.state_agrees(child['target'],child['sources'],F) or not 0<=len(F)-len(child['sources'])<=b):return False
        return True
    assert table_valid(rows)
    bad=[dict(x) for x in rows];bad[1]['returned']=None;bad[1]['provided_contract']=True
    assert not table_valid(bad)
    catches.append({'id':'supplied-boolean-with-failed-feasible-query','caught':not table_valid(bad)})
    def attained(F):return I.state_agrees(child['target'],child['sources'],F) and len(F)-len(child['sources'])==minimum
    assert attained(rows[1]['returned']) and not attained(rows[2]['returned'])
    catches.append({'id':'residual-feasibility-is-not-minimum-attainment','caught':not attained(rows[2]['returned'])})
    out={'status':'PASS_PRE_CANDIDATE_RUNTIME_AND_CHILD_CONTRACT_ADDENDUM','utc':datetime.now(timezone.utc).isoformat(),'candidate_contact':False,'candidate_compilation':False,'public_runtime_cases':len(checks),'checks':checks,'false_catches':len(catches),'catches':catches,'child_enumerated_labels':labels,'child_partition_count':15,'child_finite_minimum':minimum,'child_contract_rows':rows,'interpretation':'finite test table only; no general ResidualSolverContract or recursive implementation supplied','elapsed_seconds':time.monotonic()-start,'all_main_milestones':'OPEN','replication_count_added':0}
    p=ROOT/'research/rmaf/results/algorithm-maf-grouped-prerelease-addendum-v2.json';p.write_text(json.dumps(out,indent=2)+'\n');print(out['status'],len(checks),len(catches),out['elapsed_seconds'])
if __name__=='__main__':main()
