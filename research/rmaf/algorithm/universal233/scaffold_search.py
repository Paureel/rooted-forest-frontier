"""One-shot targeted actual-hard-child scaffold development search.

Existing tools checked: BootLoops index has no exact rooted-MAF core/scaffold
search; this wraps existing source predicates, rooted graph oracle, labelled
source-tree generator and completed multicolor prototype. All are DEVELOPMENT
contacts; this is not independent certification and does not repeat X0.
"""
from pathlib import Path
import sys,json,time,hashlib,argparse
from itertools import combinations
from fractions import Fraction
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path[:0]=[str(HERE.parent/'x0'),str(HERE.parent/'x0/multicolor'),str(ROOT/'branching')]
from fresh_oracle import Tree,applicability,tidy,forest_to_reference,validate_partition
from prototype import generate
from exact_search import trees


def classify(raw,forest):
    t=Tree(raw);fs=[Tree(f) for f in forest]
    blocks=[sorted(f.labels) for f in fs]
    spans=[t.span(b) for b in blocks]
    pairs=[[i,j] for i in range(len(fs)) for j in range(i+1,len(fs)) if spans[i]&spans[j]]
    homo=[t.clusters(f.labels)==f.clusters(f.labels) for f in fs]
    isolated=[i for i in range(len(fs)) if not any(i in p for p in pairs)]
    return {'blocks':blocks,'overlap_pairs':pairs,'homeomorphic':homo,'isolated':isolated}


def covers(partition,cores):
    return any(all(any(set(b)<=set(c) for c in e['partition']) for b in partition) for e in cores)


def controls():
    pin=json.loads((HERE/'SCAFFOLD-SEARCH-PIN-v2.json').read_text());rows=[]
    c=pin['controls'][0];r=classify(c['T'],c['forest'])
    assert r['overlap_pairs']==c['expected']['overlap_pairs']
    assert r['isolated']==[c['expected']['isolated']]
    assert r['homeomorphic']==c['expected']['homeomorphic'];rows.append({'name':c['name'],'pass':True,'observed':r})
    c=pin['controls'][1];co={int(k):v for k,v in c['colors'].items()};r=generate(c['source'],co)
    costs=sorted(e['cost'] for e in r['cores']);mass=sum(Fraction(1,2)**d for d in costs)
    assert costs==c['expected']['costs'] and str(mass)==c['expected']['mass2'];rows.append({'name':c['name'],'pass':True,'costs':costs,'mass2':str(mass)})
    c=pin['controls'][2];bad=generate(c['source'],co,omit_first_mixed_right=True)
    assert covers(c['missing_partition'],r['cores'])==c['expected_clean_covered']
    assert covers(c['missing_partition'],bad['cores'])==c['expected_corrupt_covered'];rows.append({'name':c['name'],'pass':True,'corruption_caught':True})
    c=pin['controls'][3];mins=c['local_minima'];q=c['q'];unresolved=[i for i,x in enumerate(mins) if x>1]
    lower=[min(x,2) for x in mins];queries=[[i,q-sum(x for j,x in enumerate(lower) if j!=i)] for i in unresolved]
    assert queries==c['expected_unresolved_queries'] and queries[0][1]!=c['corrupted_query_budget'];rows.append({'name':c['name'],'pass':True,'queries':queries,'corruption_caught':True})
    assert len(rows)==len(pin['controls'])==4
    return rows


def depth1(raw,forest):
    t=Tree(raw);ref=forest_to_reference(t,forest);fs=[Tree(f) for f in forest]
    base=[sorted(f.labels) for f in fs]
    if validate_partition(t,ref,base)['valid']:return 0
    for i,f in enumerate(fs):
        for e in f.edges:
            blocks,empty=f.cut_blocks([e])
            if empty:continue
            p=[b for j,old in enumerate(base) if j!=i for b in [old]]+blocks
            if validate_partition(t,ref,p)['valid']:return 1
    return None


def scan_child(raw,source,cherry):
    a,b=Tree(raw),Tree(source)
    ps=b.pendant(*cherry)
    if len(ps)!=2:return None
    blocks,empty=b.cut_blocks([p['edge'] for p in ps])
    if empty:return None
    reduced=tidy(raw,[b.restriction(c) for c in blocks]);fs=reduced['forest_trees']
    if len(fs)!=3:return None
    cl=classify(reduced['T'],fs)
    if len(cl['overlap_pairs'])!=1 or len(cl['isolated'])!=1:return None
    isolated=cl['isolated'][0]
    if not cl['homeomorphic'][isolated]:return None
    pair=cl['overlap_pairs'][0]
    if all(cl['homeomorphic'][i] for i in pair):return None # earlier rule7
    t=Tree(reduced['T']);spans=[t.span(c) for c in cl['blocks']]
    shared=spans[pair[0]]&spans[pair[1]]
    boundary=[]
    for e in t.edges:
        if set(e)<=shared:
            far=t.below[e[1]];branches=[]
            for i in pair:
                f=Tree(fs[i]);co={x:int(x in far) for x in f.labels}
                if len(set(co.values()))!=2:raise AssertionError('bad overlap boundary')
                core=generate(fs[i],co);em=[]
                for c in core['cores']:
                    nextforest=[ft for j,ft in enumerate(fs) if j!=i]+[f.restriction(p) for p in c['partition']]
                    sub=tidy(reduced['T'],nextforest)
                    state=classify(sub['T'],sub['forest_trees'])
                    em.append({'source':i,'cost':c['cost'],'partition':c['partition'],'cuts':c['cuts'],
                               'reduced':sub,'classification':state,'depth1':depth1(sub['T'],sub['forest_trees'])})
                branches.append({'source':i,'costs':[e['cost'] for e in em],'emissions':em})
            expensive=any(min(c['costs'])>=2 for c in branches)
            if expensive:
                c=Fraction(233,100);rawmass=sum(c**(-e['cost']) for br in branches for e in br['emissions'])
                unresolved=[e for br in branches for e in br['emissions'] if e['depth1'] is None]
                livemass=sum(c**(-e['cost']) for e in unresolved)
                boundary.append({'edge':e,'branches':branches,'raw_full_mass':str(2/c+rawmass/c**2),
                                 'unresolved_after_depth1_full_mass':str(2/c+livemass/c**2)})
    return {'original_T':raw,'original_Tprime':source,'cherry':list(cherry),'pendants':ps,
            'reduced':reduced,'classification':cl,'expensive_boundaries':boundary}


def caterpillar(n):
    t=[n-2,n-1]
    for i in range(n-3,-1,-1):t=[t,i]
    return t


def run(n,cap=None):
    start=time.perf_counter();raw=caterpillar(n);ta=Tree(raw);rows=[]
    count={'source_trees':0,'earlier_excluded_both_orientations':0,'actual_hard_cherries':0,'pair_isolated_good_states':0,'expensive_boundaries':0}
    for source in trees(tuple(range(n))):
        if cap is not None and count['source_trees']>=cap:break
        count['source_trees']+=1;tb=Tree(source)
        ab=applicability(ta,tb)
        if not ab['excluded_2a_to_2d']:continue
        ba=applicability(tb,ta)
        if not ba['excluded_2a_to_2d']:continue
        count['earlier_excluded_both_orientations']+=1
        for left,right,adm in [(raw,source,ab),(source,raw,ba)]:
            for r in adm['rows']:
                if r['t']!=2:continue
                count['actual_hard_cherries']+=1
                out=scan_child(left,right,r['cherry'])
                if out is not None:
                    count['pair_isolated_good_states']+=1
                    count['expensive_boundaries']+=len(out['expensive_boundaries'])
                    rows.append(out)
    return {'n':n,'cap':cap,'counts':count,'states':rows,'elapsed_seconds':time.perf_counter()-start,
            'scope':'Finite targeted DEVELOPMENT search; no universal/no-counterexample claim'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=6);p.add_argument('--cap',type=int);p.add_argument('--out',required=True)
    a=p.parse_args();out={'controls':controls(),'search':run(a.n,a.cap),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                       'pin_sha256':hashlib.sha256((HERE/'SCAFFOLD-SEARCH-PIN-v2.json').read_bytes()).hexdigest()}
    Path(a.out).write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'controls_passed':len(out['controls']),**{k:v for k,v in out['search'].items() if k!='states'}}))
