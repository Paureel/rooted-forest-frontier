#!/usr/bin/env python3
"""One-shot follow-up using the same controlled structural checker.
Diagnostic after the first witness; not independent evidence from that checker.
"""
from reachable_trace import *

def main():
    start=time.monotonic();L=leaf
    e=pair(pair(L('x'),L('y')),pair(L('u'),L('v')))
    outside=pair(pair(L('z1'),L('z2')),pair(pair(L('b2'),L('su')),pair(L('sy'),L('sv'))))
    f1=rho(pair(pair(pair(pair(L('a'),L('c')),L('d')),e),outside))
    b1=pair(L('z1'),pair(L('d'),L('z2')))
    r=pair(pair(pair(L('a'),b1),L('b2')),L('c'))
    f2=rho(pair(pair(pair(L('x'),r),pair(L('u'),L('su'))),pair(pair(L('y'),L('sy')),pair(L('v'),L('sv')))))
    trace=[]
    for ep,ec,cl,credit in [(('a','c'),'A2BC','c',[0,0]),(('a','d'),'A2BC','d',[1,0]),(('x','y'),'A3BC','y',[1,0]),(('u','v'),'A3BC','v',[2,1]),(('x','u'),'A2BC',None,[3,2])]:
        pairs,selection=eligible_pairs(f1,f2)
        assert any(set(p)==set(ep) for p in pairs),(pairs,ep)
        info=classify(f1,f2,ep);assert info['case']==ec,info
        row={'F1':newick(f1),'F2':newick(f2),'protected_F1':protected(f1),'protected_F2':protected(f2),
             'P_Q_cardinalities':credit,'selection':selection,**info};trace.append(row)
        if cl:
            branch=next(b for b in info['branches'] if b['cuts']==[cl]);assert branch['legal']
            if ep in [('x','y'),('u','v')]:assert len(info['branches'])==3 and all(b['legal'] for b in info['branches'])
            row['chosen_branch']=branch['name']
            f2=cut(mark(f2,branch['protect2']),cl);f1=cut(mark(f1,branch['protect1']),cl)
    out={'scope':'reachable count-three credit state under literal p123 union rule; not total-runtime counterexample',
         'leaf_count_excluding_rho':len(labels(f1))-1+4,'trace':trace,'elapsed_seconds':time.monotonic()-start,
         'finding':'G4.2 three-way A3BC C-child gives P={a,x,u},Q={x,u}; |P|=3 violates stated cap2.'}
    (ROOT/'results/thesis-complexity-three-credit-trace.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'trace_cases':[r['case'] for r in trace],'final_P_size':3,'elapsed_seconds':out['elapsed_seconds']}))
if __name__=='__main__':main()
