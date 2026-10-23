"""A new candidate check, reusing the controlled earlier raw-edge oracle."""
import json,pathlib,sys,time
BASE=pathlib.Path('/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf');HERE=BASE/'thesis_correctness/repair';sys.path.insert(0,str(HERE.parent))
from algorithm import Forest
from local_obligations import controls,all_optimal_cuts,info,component_data
from replay import trees

def clusters(f):
    ans={}
    def go(v):
        x=set([f.label[v]]) if v in f.label else set()
        for c in f.child[v]:x|=go(c)
        ans[v]=frozenset(x);return x
    childset={v for cs in f.child.values() for v in cs}
    for v in set(f.child)-childset:go(v)
    return ans

def common_internal(f1,f2):
    c1,c2=clusters(f1),clusters(f2);proper={v for cs in f2.child.values() for v in cs};ans=[]
    for v in proper:
        A=c2[v]
        if len(A)<2 or A not in c1.values():continue
        if info(f1,A)[0]!=info(f2,A)[0]:continue
        internal={e for e in proper if c2[e]<A}
        ans.append((v,A,internal))
    return ans

def main():
    start=time.perf_counter();controls();spec=json.loads((HERE/'common-subtree-minimum-candidate.json').read_text());ctl=spec['positive_control']
    f1,f2=Forest.tree(ctl['t1']),Forest.tree(ctl['t2']);d,opts=all_optimal_cuts(f1,f2);assert d==ctl['expected_optimum'];control_optimum=d
    A=frozenset(frozenset([x]) for x in ctl['common_cluster']);target=next(t for t in common_internal(f1,f2) if t[1]==A)
    assert all(not(e&target[2]) for e in opts)
    all_leaf_cuts={v for v,l in f2.label.items() if 'rho' not in l};assert all_leaf_cuts&target[2]
    assert all(len(b)==1 for b in component_data(f2,all_leaf_cuts))
    rows=[];fail=[]
    for n in [3,4]:
        stage=time.perf_counter();pair_count=minimums=tests=0
        family=trees(tuple('abcd'[:n]))
        for t1 in family:
          for t2 in family:
            pair_count+=1;g1,g2=Forest.tree(t1),Forest.tree(t2);d,es=all_optimal_cuts(g1,g2);minimums+=len(es)
            for v,A,internal in common_internal(g1,g2):
              for e in es:
                tests+=1
                if e&internal:fail.append({'T1':t1,'T2':t2,'optimum':d,'E':sorted(e),'common_labels':sorted(next(iter(x)) for x in A),'internal_cut':sorted(e&internal)})
        rows.append({'n':n,'pairs':pair_count,'minimum_cutsets':minimums,'common_subtree_minimum_checks':tests,'seconds':time.perf_counter()-stage})
    assert not fail,fail
    out={'status':'candidate-finite-no-fire','positive_control_optimum':control_optimum,'negative_all_AF_claim_refuted':True,'runs':rows,'failures':fail,'scope':spec['scope'],'limitation':'Same-author raw-edge oracle reused. Connected original inputs only; no universal theorem or new independent verification.','total_seconds':time.perf_counter()-start}
    p=BASE/'results/thesis-correctness-repair-common-subtree-candidate.json';p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'runs':rows,'failures':len(fail),'receipt':str(p)}))
if __name__=='__main__':main()
