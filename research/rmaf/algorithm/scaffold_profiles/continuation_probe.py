"""One-shot small-profile continuation DEVELOPMENT evaluator on frozen contacts.
Wraps controlled existing graph/core instruments; no independence claim and
no global optimum oracle. Fitch calls are only on isolated all-good groups.
"""
from pathlib import Path
from fractions import Fraction
from itertools import combinations
from functools import lru_cache
import json,sys,time,argparse,hashlib
sys.path.insert(0,str(Path(__file__).resolve().parent))
import profile_probe as pp
O=pp.oracle; C=pp.core;c=pp.c;ROOT=pp.ROOT

def canon(p):return tuple(sorted(tuple(sorted(b)) for b in p))
def local_depth1(t,s):
    a,b=O.Tree(t),O.Tree(s)
    if a.clusters(a.labels)==b.clusters(b.labels):return {'value':0,'tested_edges':0}
    tested=[]
    for edge in b.edges:
        blocks,empty=b.cut_blocks([edge])
        if empty:continue
        v=O.validate_partition(a,b,blocks)
        tested.append({'edge':edge,'valid':v['valid']})
        if v['valid']:return {'value':1,'cut':edge,'tested_edges':len(tested)}
    return {'value':None,'lower_bound':2,'tested_edges':len(tested),'edges':tested}
def geometry(target,forest):
    t=O.Tree(target);fs=[O.Tree(f) for f in forest];bs=[f.labels for f in fs]
    spans=[t.span(b) for b in bs]
    overlap=[(i,j) for i in range(len(fs)) for j in range(i) if spans[i]&spans[j]]
    good=[t.clusters(b)==f.clusters(b) for f,b in zip(fs,bs)]
    todo=set(range(len(fs)));cc=[]
    while todo:
        group={min(todo)};todo-=group
        while True:
            add={v for u,v in overlap if u in group and v in todo}|{u for u,v in overlap if v in group and u in todo}
            if not add:break
            group|=add;todo-=add
        cc.append(sorted(group))
    return t,fs,spans,overlap,good,cc

def matching_cuts(source,parts):
    s=O.Tree(source);d=len(parts)-1;wanted=canon(parts)
    for cuts in combinations(s.edges,d):
        b,e=s.cut_blocks(cuts)
        if not e and canon(b)==wanted:return [list(x) for x in cuts]
    raise AssertionError(('no true cut witness',source,parts))

def fitch_group(target,forest):
    fs=[O.Tree(f) for f in forest];labels=set().union(*(f.labels for f in fs))
    t=O.Tree(O.Tree(target).restriction(labels));col={x:i for i,f in enumerate(fs) for x in f.labels};states=range(len(fs))
    @lru_cache(None)
    def dp(v,state):
        if not t.child[v]:return 0 if col[next(x for x,w in t.leaf.items() if w==v)]==state else 10**6
        return sum(min(dp(w,s)+int(s!=state) for s in states) for w in t.child[v])
    assignment={}
    def assign(v,state):
        assignment[v]=state
        for w in t.child[v]:assign(w,min(states,key=lambda s:(dp(w,s)+int(s!=state),s)))
    assign('',min(states,key=lambda s:(dp('',s),s)))
    cuts=[e for e in t.edges if assignment[e[0]]!=assignment[e[1]]]
    parts,empty=t.cut_blocks(cuts);assert not empty
    assert len(cuts)==dp('',assignment[''])
    assert all(len({col[x] for x in b})==1 for b in parts)
    source=O.forest_to_reference(t,forest)
    assert O.validate_partition(t,source,parts,refinement=[list(f.labels) for f in fs])['valid']
    source_cuts=[]
    for i,f in enumerate(fs):
        p=[b for b in parts if set(b)<=f.labels]
        source_cuts.append({'parent':i,'parts':p,'cuts':matching_cuts(f.raw,p)})
    actual=sum(len(r['cuts']) for r in source_cuts)
    assert actual==len(parts)-len(fs)==len(cuts)-(len(fs)-1)
    return {'parents':len(fs),'target_cuts':cuts,'target_coloring_score':len(cuts),
            'additional_source_cuts':actual,'source_realizations':source_cuts,'parts':parts}

def continuation(target,forest):
    t,fs,spans,overlap,good,cc=geometry(target,forest)
    completions=[];removed=set();spent=0
    for group in cc:
        if all(good[i] for i in group):
            if len(group)>=2:
                cert=fitch_group(target,[forest[i] for i in group]);assert cert['additional_source_cuts']>=1
                cert['component_indices']=group;completions.append(cert);spent+=cert['additional_source_cuts']
            removed|=set(group)
    remain=[i for i in range(len(fs)) if i not in removed]
    remaining_overlap=[list(e) for e in overlap if all(i in remain for i in e)]
    local=[];queries=[]
    if remaining_overlap:
        factor=c**(-spent)
        mode='remaining-overlap-full-state-query'
    else:
        for i in remain:
            d=local_depth1(t.restriction(fs[i].labels),fs[i].raw)
            ell=d['value'] if d['value'] is not None else 2
            local.append({'component':i,'labels':sorted(fs[i].labels),'depth1':d,'ell':ell})
        lower_total=sum(x['ell'] for x in local)
        for r in local:
            if r['depth1']['value'] is None:
                loss=spent+lower_total-r['ell']
                queries.append({'component':r['component'],'other_parent_loss':lower_total-r['ell'],'poly_completion_loss':spent,'total_loss':loss})
        factor=sum((c**(-r['total_loss']) for r in queries),Fraction())
        mode='disjoint-local-queries' if queries else 'polynomial-terminal'
    assert factor<=1,(mode,factor)
    return {'mode':mode,'pre_completion_overlap':overlap,'homeomorphic':good,'all_good_completions':completions,
            'paid_poly_cuts':spent,'remaining_overlap':remaining_overlap,'local_pretests':local,'queries':queries,
            'relative_query_mass':str(factor),'one_unit_progress':factor<=1/c}

def controls():
    t=((0,1),(2,3))
    a=fitch_group(t,[(0,2),(1,3)]);assert a['target_coloring_score']==2 and a['additional_source_cuts']==1
    assert a['additional_source_cuts']!=a['target_coloring_score']
    b=fitch_group(t,[(0,1),(2,3)]);assert b['additional_source_cuts']==0
    assert local_depth1(((0,1),2),(0,(1,2)))['value']==1
    assert local_depth1(((0,1),2),((0,1),2))['value']==0
    # Full production-path local-query plants; no simplified arithmetic substitute.
    one=continuation((((0,1),(2,3)),(4,5)),[((0,2),(1,3)),(4,5)])
    assert one['mode']=='disjoint-local-queries' and len(one['queries'])==1
    assert one['queries'][0]['total_loss']==0 and one['relative_query_mass']=='1'
    false_bonus=[dict(one['queries'][0],total_loss=1)]
    assert false_bonus!=one['queries']
    two=continuation((((0,1),(2,3)),((4,5),(6,7))),[((0,2),(1,3)),((4,6),(5,7))])
    assert len(two['queries'])==2 and [q['total_loss'] for q in two['queries']]==[2,2]
    assert Fraction(two['relative_query_mass'])==2/c**2<=1/c
    return {'overlap_good_pair':a,'disjoint_clean_twin':b,'false_Fitch_offset_caught':True,
            'triple_depth1':True,'identical_depth0':True,'false_sole_parent_bonus_caught':True,
            'sole_unresolved_full_path':one,'two_unresolved_full_path':two,'two_hard_query_mass':str(2/c**2)}

def load_fixture(n):
    names={10:'algorithm-universal233-scaffold-witness-v1.json',15:'algorithm-scaffold-adversary-H2-witness-v1.json',19:'algorithm-universal233-scaffold-hard-plant-summary-v1.json'}
    p=ROOT/'research/rmaf/results'/names[n];d=json.loads(p.read_text())
    if n==10:a,b,ch=d['witness']['original_T'],d['witness']['original_Tprime'],d['witness']['cherry']
    elif n==15:a,b,ch=d['original']['T'],d['original']['Tprime'],d['selected_cherry']
    else:a,b,ch=d['original_T'],d['original_Tprime'],d['selected_cherry']
    return a,b,ch,p

def original_lift(orig_source,initial_cuts,initial_closed,expansion,parents,parent_i,emission):
    s=O.Tree(orig_source);f=O.Tree(parents[parent_i]);labels=set().union(*(set(expansion[x]) for x in f.labels))
    mapped=[]
    for _,v in emission['cuts']:
        wanted=set().union(*(set(expansion[x]) for x in f.below[v]))
        candidates=[e for e in s.edges if set(s.below[e[1]])&labels==wanted and e not in initial_cuts and e not in mapped]
        assert candidates,('unlifted edge',v,wanted)
        mapped.append(min(candidates,key=lambda e:(len(e[1]),e)))
    actual,empty=s.cut_blocks(initial_cuts+mapped);assert not empty
    expected=[b for i,p in enumerate(parents) if i!=parent_i for b in [set().union(*(set(expansion[x]) for x in O.Tree(p).labels))]]
    expected += [set().union(*(set(expansion[x]) for x in b)) for b in emission['partition']]
    expected += initial_closed
    assert canon(actual)==canon(expected),(actual,expected)
    assert len(set(map(tuple,initial_cuts+mapped)))==len(initial_cuts)+emission['cost']
    return {'fixed_pendant_cuts':initial_cuts,'core_cuts_original':mapped,'original_partition':actual,'no_leafless_regions':True}

def fixture(n):
    t0,s0,ch,path=load_fixture(n);t0g,s0g=O.Tree(t0),O.Tree(s0)
    admission=[O.applicability(t0g,s0g),O.applicability(s0g,t0g)]
    assert all(x['excluded_2a_to_2d'] for x in admission)
    assert sorted(ch) in t0g.cherries()
    pend=s0g.pendant(*ch);assert len(pend)==2
    fixed=[tuple(p['edge']) for p in pend];blocks,empty=s0g.cut_blocks(fixed);assert not empty
    initial=O.tidy(t0,[s0g.restriction(b) for b in blocks]);t,fs,spans,overlap,good,cc=geometry(initial['T'],initial['forest_trees'])
    assert len(overlap)==1
    i,j=overlap[0];outside=set(range(len(fs)))-{i,j};assert all(good[k] for k in outside)
    selectors=[];seen=set()
    # All actual shared vertices; equivalent color partitions are deduplicated.
    for v in sorted(spans[i]&spans[j],key=lambda v:(len(v),v)):
        if v in t.leaf.values():continue
        colors=[];signature=[]
        for parent in (i,j):
            col={x:(int(t.leaf[x][len(v)])+1 if t.leaf[x].startswith(v) else 0) for x in fs[parent].labels}
            groups=canon([[x for x in col if col[x]==a] for a in sorted(set(col.values()))])
            assert len(groups)>=2
            colors.append(col);signature.append(groups)
        signature=tuple(signature)
        if signature in seen:continue
        seen.add(signature);branches=[];total=Fraction()
        for parent,col in zip((i,j),colors):
            r=C.generate(fs[parent].raw,col);profile=sorted(e['cost'] for e in r['raw_cores']);ems=[]
            for e in r['raw_cores']:
                lift=original_lift(s0,fixed,initial['closed_components'],initial['expansion'],initial['forest_trees'],parent,e)
                next_f=[f.raw for k,f in enumerate(fs) if k!=parent]+[fs[parent].restriction(b) for b in e['partition']]
                clean=O.tidy(t.raw,next_f);cnt=continuation(clean['T'],clean['forest_trees'])
                rel=Fraction(cnt['relative_query_mass']);total+=c**(-e['cost'])*rel
                ems.append({'cost':e['cost'],'partition':e['partition'],'original_cut_lift':lift,'tidying':clean,'continuation':cnt})
            branches.append({'parent':parent,'colors':col,'raw_profile':profile,'emissions':ems})
        raw=2/c+sum((pp.mass(b['raw_profile']) for b in branches),Fraction())/c**2
        full=2/c+total/c**2
        selectors.append({'target_vertex':v,'color_groups':signature,'branches':branches,'raw_full_mass':str(raw),
            'continued_full_mass':str(full),'passes':full<1,'single_progress_emissions':sum(e['continuation']['one_unit_progress'] for b in branches for e in b['emissions'])})
    assert selectors
    return {'n':n,'development_contact':str(path.relative_to(ROOT)),'contact_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'initial':initial,'admission':admission,'selectors':selectors,'any_selector_passes':any(x['passes'] for x in selectors),
            'all_selectors_pass':all(x['passes'] for x in selectors)}

def main():
    p=argparse.ArgumentParser();p.add_argument('--n',nargs='+',type=int,required=True);p.add_argument('--output',required=True);p.add_argument('--pilot');a=p.parse_args()
    out=ROOT/a.output
    if out.exists():raise FileExistsError(out)
    if a.n!=[10]:assert a.pilot and json.loads((ROOT/a.pilot).read_text())['controls']
    start=time.monotonic();ct=controls();rows=[]
    for n in a.n:
        ts=time.monotonic();r=fixture(n);r['seconds']=time.monotonic()-ts;rows.append(r)
        print(json.dumps({'n':n,'selectors':len(r['selectors']),'all_pass':r['all_selectors_pass'],'rows':[
            {'v':x['target_vertex'],'profiles':[b['raw_profile'] for b in x['branches']],'raw':x['raw_full_mass'],'continued':x['continued_full_mass'],'progress':x['single_progress_emissions']} for x in r['selectors']], 'seconds':r['seconds']}),flush=True)
    result={'scope':'DEVELOPMENT fixed-contact true-cut/continuation calculation; source-rule safety, universal progress and complete algorithm OPEN',
            'controls':ct,'rows':rows,'seconds':time.monotonic()-start}
    result['source_sha256']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),Path(pp.__file__),ROOT/'research/rmaf/algorithm/x0/fresh_oracle.py',ROOT/'research/rmaf/algorithm/x0/multicolor/prototype.py']}
    out.write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
