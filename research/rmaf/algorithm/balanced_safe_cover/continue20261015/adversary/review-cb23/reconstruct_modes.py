#!/usr/bin/env python3
"""One-shot review continuation; preserve frozen comparator and trace closure ambiguity.
The full-fixed-point compiler is the independently frozen preimplementation design.
The literal stop-on-nonsingleton variant is written AFTER parent code contact;
its use is explicitly recorded and cannot retroactively strengthen independence.
"""
import sys,json,time,hashlib,itertools,copy
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
import compare_cb23 as C
X=C.X
ROOT=Path('research/rmaf/algorithm/balanced_safe_cover/continue20261015')
RECEIPT=Path('research/rmaf/results/algorithm-balanced-cover-continue-cb3-obstruction.json')
OUT=Path('research/rmaf/results/algorithm-balanced-cover-continue-review-cb23-source-modes-v1.json')
ORIGINAL_CLOSE=C.close

def literal_stop_close(H):
    rows=X.minimal(H);forced=[];steps=[]
    while rows:
        rows=X.quotient(rows)
        h=min(rows,key=lambda z:(z.bit_count(),z))
        if h.bit_count()!=1:break
        e=h.bit_length()-1;assert e not in forced
        forced.append(e);steps.append({'edge':e,'rows_before':list(rows)})
        rows=tuple(q for q in rows if not q>>e&1)
    return {'rows':list(rows),'forced':forced,'steps':steps}

def project_profile(P):
    return {'row':P['row'],'raw_prefixes':[(c['branch_edge'],c['cut_mask'],c['delta']) for c in P['raw']],'kept_prefixes':[(c['branch_edge'],c['cut_mask'],c['delta']) for c in P['kept']],'mass':P['mass']}

def profiles_for(close,H):
    C.close=close
    return [C.compile_row(H,h) for h in H]

def main():
    start=time.perf_counter();R=json.loads(RECEIPT.read_text());S,T=X.Tree(R['source']),X.Tree(R['target']);oldH=X.conflicts(S,T)
    ids={frozenset(e['child_labels']):e['edge'] for e in R['original_source_edges']};M={e:ids[L] for e,L in C.edge_clades(S).items()};assert len(M)==len(set(M.values()))==10
    H=X.minimal(tuple(C.remap(h,M) for h in oldH));closed=ORIGINAL_CLOSE(H);assert closed['forced']==[] and closed['rows']==R['minimal_projected_conflicts'];H=closed['rows'];assert len(H)==26
    v,P=X.partition_opt(S,T);assert v==3
    for mask in range(1<<10):
        part,_=S.cut_partition(mask);assert X.agreement(S,T,part)==all(mask&h for h in oldH)
    # Freeze and compare both exact transition interpretations.
    strong=profiles_for(ORIGINAL_CLOSE,H);literal=profiles_for(literal_stop_close,H)
    diffs=[]
    for A,B,P in zip(strong,literal,R['all_rows']):
        assert C.external(B)==P
        assert project_profile(A)==project_profile(B)
        if C.external(A)!=P:diffs.append({'row':A['row'],'strong':C.external(A),'literal_receipt':P})
    # Parent implementation trace, after prior comparator gate and strict replay failure.
    sys.path.insert(0,str(ROOT.resolve()))
    import conflict_dag_solver as dag
    import conflict_row_selector as selector
    parent_root,pcuts,psteps=dag.forced_closure(tuple(X.minimal(tuple(C.remap(h,M) for h in oldH))))
    assert list(parent_root)==H and pcuts==0 and psteps==[]
    parent_best,parent_profiles=selector.choose_row(tuple(H));assert len(parent_profiles)==26
    for A,B in zip(literal,parent_profiles):assert C.external(A)==selector.json_safe(B)
    best=min(strong,key=lambda a:(Fraction_mass(a),a['row']));assert best['row']==960 and Fraction_mass(best)==C.Fraction(9,7)
    assert all(sum(c['delta']==1 for c in P['kept'])>=3 for P in strong)
    C.close=ORIGINAL_CLOSE
    implication_checks=0
    for profiles in (strong,literal):
        states=sorted({tuple(c['rows']) for P in profiles for c in P['raw']})
        for A in states:
            for B in states:
                assert C.implies(A,B)==C.truth_implies(A,B,10);implication_checks+=1
        for P in profiles:
            for child in P['raw']:
                assert child['delta']==child['cut_mask'].bit_count()==len(child['cuts'])==len(set(child['cuts']))
            for pr in P['prunes']:
                A=next(c for c in P['raw'] if c['branch_edge']==pr['dominator']);B=next(c for c in P['raw'] if c['branch_edge']==pr['pruned']);assert C.dominates(A,B)
    corruptions=[]
    for kind in ['delta','mass','row']:
        Q=copy.deepcopy(R['all_rows'])
        if kind=='delta':Q[0]['raw'][0]['delta']-=1
        if kind=='mass':Q[0]['mass']['numerator']+=1
        if kind=='row':Q[0]['raw'][0]['rows'][0]^=1
        assert [C.external(P) for P in literal]!=Q;corruptions.append(kind)
    source_clades=set(C.edge_clades(S).values());target_clades=set(C.edge_clades(T).values());common=[sorted(B) for B in source_clades&target_clades if len(B)>1]
    assert common==[]
    result={'status':'PRIMARY_OBSTRUCTION_CONFIRMED_WITH_CLOSURE_INTERPRETATION_NOTE','source':R['source'],'target':R['target'],'source_edge_map':M,'independent_source_rows_old_ids':oldH,'mapped_source_minimal_rows':X.minimal(tuple(C.remap(h,M) for h in oldH)),'closed_root_rows':H,'original_optimum_by_partitions':v,'finite_C1_source_cutsets_checked':1024,'all_rows':26,'strong_fixed_point_profiles':strong,'literal_stop_profiles':literal,'strict_row_state_mismatches':diffs,'strict_profile_mismatch_count':len(diffs),'primary_prefix_and_mass_profiles_match_all_26':True,'minimum_unit_children':min(sum(c['delta']==1 for c in P['kept']) for P in strong),'best_row':best['row'],'best_mass':[9,7],'semantic_implication_pairs_checked':implication_checks,'stored_corruptions_caught':corruptions,'common_nontrivial_pendant_clades':common,'parent_profiles_exactly_replayed':True,'seconds':time.perf_counter()-start,'lineage':{'preimplementation_comparator_sha256':hashlib.sha256((Path(__file__).parent/'compare_cb23.py').read_bytes()).hexdigest(),'postimplementation_mode_wrapper_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'receipt_sha256':hashlib.sha256(RECEIPT.read_bytes()).hexdigest(),'primary_fixed_point_claims':'independent preimplementation code, source/spec/receipt inputs shared','literal_state_replay':'code contact declared; not a blinded second implementation'}}
    assert result['seconds']<10
    OUT.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['status','all_rows','original_optimum_by_partitions','strict_profile_mismatch_count','minimum_unit_children','best_row','best_mass','semantic_implication_pairs_checked','parent_profiles_exactly_replayed','seconds']}))

def Fraction_mass(P):return C.Fraction(P['mass']['numerator'],P['mass']['denominator'])
if __name__=='__main__':main()
