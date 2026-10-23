#!/usr/bin/env python3
"""One-shot bounded original-optimum extension trace for six compiled CB4 runs."""
import sys,json,itertools,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
import review_cb4 as R
X,G=R.X,R.G
OUT=Path('research/rmaf/results/algorithm-balanced-cover-continue-review-cb4-dominance-v1.json')

def hits(K,H):return all(K&h for h in H)
def dominates(A,B):return A['delta']<=B['delta'] and all(any(hj&hi==hj for hj in B['rows']) for hi in A['rows'])
def original_min_cuts(M,opt):
    inverse={e:p for p,e in M.SE.items()};result=[]
    for edges in itertools.combinations(range(len(M.S.edges)),opt):
        cuts=set(edges);P=R.graph_parts(M.S,M.S.adj,cuts)
        if all(L for L,V in P) and X.agreement(M.S,M.T,tuple(L for L,V in P)):
            result.append(sum(1<<inverse[e] for e in edges))
    assert result
    return result

def check_original(M,K,opt):
    cuts={M.SE[e] for e in range(K.bit_length()) if K>>e&1};P=R.graph_parts(M.S,M.S.adj,cuts)
    assert len(cuts)==opt and all(L for L,V in P) and X.agreement(M.S,M.T,tuple(L for L,V in P))

def main():
    t=time.perf_counter();finite=json.load(open('research/rmaf/results/algorithm-balanced-cover-continue-review-cb4-covers-v1.json'));fixtures={f['id']:f for f in json.load(open(R.BASE.parent/'CONTROLS-frozen-v1.json'))['ordinary']};records=[];totals={'compiled_nodes':0,'relevant_optimum_nodes':0,'good_raw_branch_witnesses':0,'retained_substitution_checks':0,'guarded_full_minima_checked':0}
    checked_full=set()
    for case in finite['rows']:
        if not case['generation']['stats']['row_candidates_compiled']:continue
        f=fixtures[case['id']];b=case['budget'];M=R.Model(f['source'],f['target'],b);opt=f['optimum'];Ks=original_min_cuts(M,opt);trace=[];current={'C':None}
        oldguard=G.guard;oldchoose=G.selector.choose_row
        def guard(S,T,budget,C):
            current['C']=C
            return oldguard(S,T,budget,C)
        def choose(H):
            chosen,allrows=oldchoose(H);trace.append({'C':current['C'],'rows':list(H),'chosen':chosen});return chosen,allrows
        saved={n:getattr(R.PRODUCTION,n) for n in ['partitions','oracle','packing','exact_row']}
        def banned(*a,**kw):raise AssertionError('generation used scoring oracle')
        try:
            G.guard=guard;G.selector.choose_row=choose
            for n in saved:setattr(R.PRODUCTION,n,banned)
            output=G.generate(f['source'],f['target'],b)
        finally:
            G.guard=oldguard;G.selector.choose_row=oldchoose
            for n,q in saved.items():setattr(R.PRODUCTION,n,q)
        assert output==case['generation']
        seen=[]
        for node in trace:
            C,H,chosen=node['C'],node['rows'],node['chosen'];totals['compiled_nodes']+=1
            extensions=[K for K in Ks if C&K==C and hits(K&~C,H)]
            record={'prefix':C,'row':chosen['row'],'retained_branches':[c['branch_edge'] for c in chosen['kept']],'original_minimum_extensions':len(extensions),'good_raw':[]}
            if extensions:
                totals['relevant_optimum_nodes']+=1
                for raw in chosen['raw']:
                    J=raw['cut_mask'];assert J.bit_count()==raw['delta'] and not J&C
                    good=[K for K in extensions if K&J==J and hits(K&~(C|J),raw['rows'])]
                    if not good:continue
                    record['good_raw'].append({'edge':raw['branch_edge'],'extensions':len(good)})
                    retained=[i for i in chosen['kept'] if dominates(i,raw)];assert retained
                    for K in good:
                        totals['good_raw_branch_witnesses']+=1;W=K&~(C|J)
                        for keep in retained:
                            I=keep['cut_mask'];assert not C&I and I.bit_count()==keep['delta']
                            replacement=C|I|W
                            assert replacement.bit_count()<=K.bit_count()==opt
                            check_original(M,replacement,opt)
                            assert replacement&I==I and replacement&C==C
                            totals['retained_substitution_checks']+=1
                assert record['good_raw']
            seen.append(record)
        if case['id'] not in checked_full:
            for K in Ks:
                cert=G.guard(M.PS,M.PT,b,K);assert cert is not None
                ok,D=R.check(M,b,cert);assert ok,D
                assert cert['original_unmarked_tau_upper_bound']==0
                totals['guarded_full_minima_checked']+=1
            checked_full.add(case['id'])
        records.append({'id':case['id'],'budget':b,'original_minimum_cutsets':len(Ks),'nodes':seen})
    assert len(records)==6
    result={'status':'FINITE_PREFIX_DOMINANCE_EXTENSION_TRACE_PASS','runs':len(records),'totals':totals,'records':records,'seconds':time.perf_counter()-t,'scope':'six previously compiled frozen-input runs only; conditional invariant review, not universal formal proof'}
    assert result['seconds']<10
    OUT.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['status','runs','totals','seconds']}))
if __name__=='__main__':main()
