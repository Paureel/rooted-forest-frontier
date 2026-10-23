"""One-shot deletion-minimizer for the cut-only chain candidate; no new oracle."""
from chain import *
from itertools import combinations


def paid_chain_score(raw,other,cherry,use_earlier_rules=False):
    a,b=Tree(raw),Tree(other)
    if not applicability(a,b)['excluded_2a_to_2d'] or not applicability(b,a)['excluded_2a_to_2d']:
        return {'admitted':False,'reason':'Figure16 earlier rule'}
    row=next(r for r in applicability(a,b)['rows'] if r['cherry']==cherry)
    blocks,empty=b.cut_blocks([p['edge'] for p in row['pendants']])
    assert not empty and len(blocks)==3
    reduced=tidy(raw,[b.restriction(c) for c in blocks]);fs=reduced['forest_trees']
    if len(fs)!=3:
        return {'admitted':False,'reason':'not three live'}
    t=Tree(reduced['T']);spans=[t.span(c) for c in reduced['forest_blocks']]
    es=[span_edges(t,c) for c in reduced['forest_blocks']]
    pairs=[(i,j) for i in range(3) for j in range(i) if es[i]&es[j]]
    if len(pairs)!=2:
        return {'admitted':False,'reason':'not chain'}
    middle=set(pairs[0])&set(pairs[1]);assert len(middle)==1
    bi=middle.pop();ai,ci=[i for i in range(3) if i!=bi]
    assert not spans[ai]&spans[ci]
    homeomorphic=[t.clusters(c)==Tree(ft).clusters(c)
                 for c,ft in zip(reduced['forest_blocks'],fs)]
    if use_earlier_rules and all(homeomorphic):
        return {'admitted':False,'reason':'earlier rule7 all-homeomorphic chain',
                'reduced':reduced,'homeomorphic':homeomorphic}
    rows=[]
    for e,f in product(sorted(es[ai]&es[bi]),sorted(es[ci]&es[bi])):
        emitted=chain_cover(t,fs,ai,bi,ci,e,f)
        unique={signature(x['blocks']):x for x in emitted}
        minimal=[x for x in unique.values() if not any(y['paid']<x['paid']
                 and all(any(set(bb)<=set(cc) for cc in y['blocks']) for bb in x['blocks'])
                 for y in unique.values())]
        vector=[1,1,*[2+x['paid'] for x in minimal]]
        mass=sum(Fraction(100,231)**d for d in vector)
        rows.append({'AB_edge':e,'BC_edge':f,'full_vector':vector,'mass':str(mass),'fails':mass>1})
    return {'admitted':True,'reduced':reduced,'homeomorphic':homeomorphic,
            'earlier_rule7_applies':all(homeomorphic),
            'rows':rows,'all_pairs_fail':all(r['fails'] for r in rows)}


def main():
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('--version',type=int,choices=[1,2],default=1)
    version=parser.parse_args().version;earlier=version==2
    start=time.perf_counter();source=json.loads((HERE/'CHAIN-PIN-v3.json').read_text())
    control=paid_chain_score(source['T'],source['Tprime'],source['cherry'],earlier)
    assert control['admitted'] and len(control['rows'])==3 and control['all_pairs_fail']
    assert all(r['full_vector']==[1,1,4,4,4,4] for r in control['rows'])
    twin=json.loads((HERE/'CHAIN-PIN-v2.json').read_text())
    clean=paid_chain_score(twin['T'],twin['Tprime'],twin['cherry'],earlier)
    assert clean['admitted'] and not clean['all_pairs_fail']
    bad=json.loads((HERE/'CHAIN-PIN-v1.json').read_text())
    inad=paid_chain_score(bad['T'],bad['Tprime'],bad['cherry'],earlier)
    assert not inad['admitted']
    originala,originalb=Tree(source['T']),Tree(source['Tprime'])
    rows=[];witness=None;complete=True;count=0
    for n in range(7,12):
        for rest in combinations(sorted(originala.labels-{9,10}),n-2):
            if time.perf_counter()-start>30:
                complete=False;break
            labels=sorted([9,10,*rest]);a=originala.restriction(labels);b=originalb.restriction(labels)
            scored=paid_chain_score(a,b,[9,10],earlier);count+=1
            row={'labels':labels,'n':n,'T':a,'Tprime':b,'score':scored}
            rows.append(row)
            if scored.get('all_pairs_fail') and witness is None:
                witness=row
        if not complete:break
    expected=sum(1 for n in range(7,12) for _ in combinations(range(9),n-2))
    if complete:assert count==expected
    out={'scope':'Smallest measured refuter within all pinned leaf-deletion restrictions; no global minimum claim',
         'controls':{'original_refuter':control,'passing_clean_twin':clean,'ineligible_negative':inad},
         'tested':count,'expected':expected,'complete':complete,
         'admitted_chains':sum(r['score']['admitted'] for r in rows),
         'refuters':sum(r['score'].get('all_pairs_fail',False) for r in rows),
         'smallest_refuter':witness,'rows':rows,'elapsed_seconds':time.perf_counter()-start,
         'code_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         'pin_sha256':hashlib.sha256((HERE/f'SHRINK-PIN-v{version}.json').read_bytes()).hexdigest(),
         'policy_version':version,'excludes_earlier_rule7':earlier}
    if witness:
        out['smallest_refuter_exact_replay']=run({'T':witness['T'],'Tprime':witness['Tprime'],'cherry':[9,10]})
    (ROOT/f'results/algorithm-macro-chain-minimize-v{version}.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Deletion states:',count,'/',expected,'complete:',complete)
    print('Admitted chains:',out['admitted_chains'],'refuters:',out['refuters'])
    print('Smallest refuter leaves:',witness['n'] if witness else None)
    print('Score elapsed seconds:',out['elapsed_seconds'])


if __name__=='__main__':main()
