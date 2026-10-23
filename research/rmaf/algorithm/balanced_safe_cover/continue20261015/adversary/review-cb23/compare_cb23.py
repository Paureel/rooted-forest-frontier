#!/usr/bin/env python3
"""One-shot nonauthor CB2/CB3 comparator; design frozen before production code contact."""
from pathlib import Path
from fractions import Fraction
import sys,json,time,itertools,hashlib,copy,argparse
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import independent_cb1 as X
BASE=Path(__file__).resolve().parent
OUT=Path('research/rmaf/results')

def implies(A,B):
    return all(any(a&b==a for a in A) for b in B)

def truth_implies(A,B,m):
    return all(not all(C&a for a in A) or all(C&b for b in B) for C in range(1<<m))

def close(H):
    R=X.minimal(H);forced=[];steps=[]
    while R:
        Q=X.quotient(R)
        singles=[h for h in Q if h.bit_count()==1]
        if singles:
            h=min(singles);e=h.bit_length()-1
            assert e not in forced
            forced.append(e);steps.append({'edge':e,'rows_before':list(Q)})
            R=X.minimal(tuple(hh for hh in Q if not hh>>e&1))
        elif Q==R:return {'rows':list(Q),'forced':forced,'steps':steps}
        else:R=Q
    return {'rows':[],'forced':forced,'steps':steps}

def child(H,e):
    assert any(h>>e&1 for h in H)
    C=close(tuple(h for h in H if not h>>e&1));cuts=[e]+C['forced'];assert len(cuts)==len(set(cuts))
    return {'branch_edge':e,'rows':C['rows'],'cut_mask':sum(1<<z for z in cuts),'delta':len(cuts),'forcing_steps':C['steps'],'cuts':cuts}

def dominates(A,B):return A['delta']<=B['delta'] and implies(B['rows'],A['rows'])
def order(A):return (A['delta'],A['branch_edge'],A['cut_mask'],tuple(A['rows']))
def compile_row(H,h):
    assert h in H
    raw=[child(H,e) for e in range(h.bit_length()) if h>>e&1];kept=[];prunes=[]
    for B in raw:
        D=[A for A in raw if A is not B and dominates(A,B) and (not dominates(B,A) or order(A)<order(B))]
        if D:prunes.append({'pruned':B['branch_edge'],'dominator':min(D,key=order)['branch_edge']})
        else:kept.append(B)
    kept.sort(key=order);mass=sum((Fraction(3,7)**A['delta'] for A in kept),Fraction())
    return {'row':h,'raw':raw,'kept':kept,'mass':{'numerator':mass.numerator,'denominator':mass.denominator,'greater_than_one':mass>1},'prunes':prunes}

def external(P):
    return {'row':P['row'],'raw':[{k:v for k,v in c.items() if k!='cuts'} for c in P['raw']],'kept':[{k:v for k,v in c.items() if k!='cuts'} for c in P['kept']],'mass':P['mass']}

def valid_child(H,C):
    try:
        cuts=C['cuts']
        return len(cuts)==len(set(cuts)) and C['delta']==len(cuts)==C['cut_mask'].bit_count() and C==child(H,C['branch_edge'])
    except (KeyError,TypeError,AssertionError):return False

def valid_profile(H,P):
    try:return P==compile_row(H,P['row']) and all(valid_child(H,c) for c in P['raw'])
    except (KeyError,TypeError,AssertionError):return False

def controls():
    F=json.loads((BASE/'CONTROLS-v1.json').read_text());caught=[];records=[];t=time.perf_counter()
    for C in F['closure']:
        R=close(C['rows']);assert not R['rows'] and len(R['forced'])==C['cost'];records.append({'id':C['id'],'closed':R})
    for C in F['implication']:
        assert implies(C['A'],C['B'])==truth_implies(C['A'],C['B'],2)==C['expected']
    for C in F['every_row_terminal_cost_two']:
        H=close(C['rows'])['rows']
        for h in H:
            P=compile_row(H,h);assert valid_profile(H,P);assert len(P['kept'])==1 and P['kept'][0]['delta']==2 and P['kept'][0]['rows']==[]
        records.append({'id':C['id'],'rows':H,'profiles':[compile_row(H,h) for h in H]})
    A={'delta':1,'rows':[3]};B={'delta':2,'rows':[1]};assert dominates(A,B) and not dominates(B,A)
    H=[3,5,6];P=compile_row(H,3);assert valid_profile(H,P)
    M=copy.deepcopy(P);M['raw'][0]['delta']-=1;assert not valid_profile(H,M);caught.append('delta_minus_one')
    M=copy.deepcopy(P);M['mass']['numerator']+=1;assert not valid_profile(H,M);caught.append('mass_numerator_plus_one')
    M=copy.deepcopy(P);M['raw'][0]['cuts'].append(M['raw'][0]['cuts'][0]);assert not valid_profile(H,M);caught.append('duplicate_cut')
    assert implies([1],[3]) and not implies([3],[1]);caught.append('reverse_implication')
    M=copy.deepcopy(P);M['raw'].pop();assert not valid_profile(H,M);caught.append('omit_raw_branch')
    assert not Fraction(7,3)>=Fraction(23391,10000);caught.append('false_base_comparison')
    assert sorted(caught)==sorted(F['corruptions']) and len(caught)==6
    R={'status':'CONTROLS_PASS','closure_controls':2,'implication_controls':4,'all_row_closure_controls':2,'dominance_control':True,'corruptions_caught':caught,'records':records,'seconds':time.perf_counter()-t,'instrument_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (OUT/'algorithm-balanced-cover-continue-review-cb23-controls-v1.json').write_text(json.dumps(R,indent=2)+'\n')
    print(json.dumps({k:R[k] for k in ['status','corruptions_caught','seconds','instrument_sha256']}));return R

def edge_clades(S):
    out={}
    def walk(v):
        z={a for a,u in S.leaf.items() if u==v}
        for w,e in S.adj[v]:
            if S.parent.get(w)==v:z|=walk(w)
        return z
    for e,(u,v) in enumerate(S.edges):out[e]=frozenset(walk(v))
    return out

def remap(h,M):return sum(1<<M[e] for e in range(h.bit_length()) if h>>e&1)

def source_review(path):
    t=time.perf_counter();R=json.loads(Path(path).read_text());S,T=X.Tree(R['source']),X.Tree(R['target'])
    input_map={frozenset(c['child_labels']):c['edge'] for c in R['original_source_edges']};M={e:input_map[L] for e,L in edge_clades(S).items()};assert len(set(M.values()))==len(S.edges)==10
    oldH=X.conflicts(S,T);H=X.minimal(tuple(remap(h,M) for h in oldH));C=close(H);assert C['forced']==R['forced_before_branch']==[] and C['rows']==R['minimal_projected_conflicts'];H=C['rows']
    v,P=X.partition_opt(S,T);assert v==R['original_optimum']==3
    for cut in range(1<<len(S.edges)):
        part,_=S.cut_partition(cut);assert X.agreement(S,T,part)==all(cut&h for h in oldH)
    profiles=[compile_row(H,h) for h in H];assert len(profiles)==26
    compares=[]
    for P,Q in zip(profiles,R['all_rows']):
        assert external(P)==Q,(P['row'],'profile mismatch');assert valid_profile(H,P);compares.append({'row':P['row'],'exact_match':True})
    best=min(profiles,key=lambda p:(Fraction(p['mass']['numerator'],p['mass']['denominator']),p['row']))
    assert best['row']==960 and best['mass']['numerator']==9 and best['mass']['denominator']==7 and external(best)==R['best_row']
    assert all(sum(c['delta']==1 for c in p['kept'])>=3 for p in profiles)
    # Check the actual CNF relation semantically for every distinct raw state.
    states=sorted(set(tuple(c['rows']) for p in profiles for c in p['raw']));checks=0
    for A in states:
        for B in states:
            assert implies(A,B)==truth_implies(A,B,10);checks+=1
    # A stored child-prefix witness must carry its literal number of distinct cuts.
    for P in profiles:
        for c in P['raw']:assert c['delta']==len(c['cuts'])==c['cut_mask'].bit_count() and valid_child(H,c)
    negatives=[]
    for kind in ['delta','mass','row']:
        QQ=copy.deepcopy(R['all_rows'])
        if kind=='delta':QQ[0]['raw'][0]['delta']-=1
        if kind=='mass':QQ[0]['mass']['numerator']+=1
        if kind=='row':QQ[0]['raw'][0]['rows'][0]^=1
        assert [external(p) for p in profiles]!=QQ;negatives.append(kind)
    result={'status':'SOURCE_RECONSTRUCTION_CONFIRMED','source':R['source'],'target':R['target'],'source_edge_map':M,'original_independent_rows':oldH,'mapped_original_rows':list(X.minimal(tuple(remap(h,M) for h in oldH))),'closed_root_rows':H,'source_optimum_partition_cuts':v,'finite_C1_cutsets_checked':1<<len(S.edges),'all_profiles':profiles,'profile_comparisons':compares,'best_row':best,'unit_child_counts':[sum(c['delta']==1 for c in p['kept']) for p in profiles],'distinct_child_states':len(states),'semantic_implication_pairs_checked':checks,'stored_corruptions_caught':negatives,'seconds':time.perf_counter()-t,'source_receipt_sha256':hashlib.sha256(Path(path).read_bytes()).hexdigest(),'instrument_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (OUT/'algorithm-balanced-cover-continue-review-cb23-source-v1.json').write_text(json.dumps(result,indent=2)+'\n')
    assert result['seconds']<10
    print(json.dumps({k:result[k] for k in ['status','finite_C1_cutsets_checked','distinct_child_states','semantic_implication_pairs_checked','seconds']}|{'rows':len(profiles),'minimum_unit_children':min(result['unit_child_counts']),'best_mass':[best['mass']['numerator'],best['mass']['denominator']]}))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--source');args=ap.parse_args();controls()
    if args.source:source_review(args.source)
