"""Independent graph/edge-cut review of frozen A fixtures and deletion family.
No imports from any candidate or X0 implementation. Cut-core enumeration below
uses explicit actual cut partitions, selecting every inclusion-minimal color
separator; on frozen fixtures these source separators are unique one-cut cores.
This is intentionally a different finite verifier, not Lemma1 generation proof.
"""
import itertools,json,time
from fractions import Fraction
from pathlib import Path
from independent_graph import Graph,exact,exact_forest,valid,valid_forest,priority,thaw
HERE=Path(__file__).resolve().parent; CAMPAIGN=HERE.parents[1]; OUT=CAMPAIGN/'results'
BASE=Fraction(231,100)
def write(name,data): (OUT/name).write_text(json.dumps(data,indent=2)+'\n')
def cp(blocks): return tuple(sorted(tuple(sorted(b)) for b in blocks))
def refines(fine,coarse): return all(any(set(b)<=set(c) for c in coarse) for b in fine)
def span_edges(g,block):
    s=g.span(block)
    return {e for e in g.edges if e[0] in s and e[1] in s}
def tidy(t,forest):
    labels=set(Graph(t).labels); expansions={x:[x] for x in labels}; closed=[]; history=[]
    while True:
        single=[raw for raw in forest if isinstance(raw,int)]
        if single:
            for x in single: closed.append(expansions.pop(x)); labels.remove(x)
            forest=[raw for raw in forest if not isinstance(raw,int)]
            history.append({'closed':single})
            t=Graph(t).restrict(labels) if labels else None
            if not labels: break
        common=set(Graph(t).cherries()) & set(c for f in forest for c in Graph(f).cherries())
        if not common: break
        lo,hi=min(common); expansions[lo]+=expansions.pop(hi); labels.remove(hi)
        t=Graph(t).restrict(labels)
        forest=[Graph(f).restrict(set(Graph(f).labels)-{hi}) if hi in Graph(f).labels else f for f in forest]
        history.append({'contracted':[lo,hi],'representative':lo})
    forest=sorted(forest,key=lambda f: tuple(sorted(Graph(f).labels)))
    return {'target':thaw(t),'sources':[thaw(f) for f in forest],'blocks':[sorted(Graph(f).labels) for f in forest],'expansion':expansions,'closed':closed,'history':history}
def earlier(t,forest):
    g=Graph(t); blocks=[set(Graph(f).labels) for f in forest]; spans=[g.span(b) for b in blocks]
    good=[g.topology(b)==Graph(f).topology(b) for b,f in zip(blocks,forest)]
    overlaps=[[bool(spans[i]&spans[j]) for j in range(len(forest))] for i in range(len(forest))]
    rule7=[]
    for r in range(2,len(forest)+1):
        for subset in itertools.combinations(range(len(forest)),r):
            if all(good[i] for i in subset) and not any(overlaps[i][j] for i in subset for j in range(len(forest)) if j not in subset):
                rule7.append(list(subset))
    rule6=[]
    if len(forest)==3:
        for a,b,c in itertools.permutations(range(3)):
            if good[a] and good[c] and not good[b] and not overlaps[c][a] and not overlaps[c][b] and len(span_edges(g,blocks[a])&span_edges(g,blocks[b]))==1:
                rule6.append([a,b,c])
    return {'homeomorphic':good,'rule6':rule6,'rule7':rule7,'vertex_overlaps':overlaps}
def prepare(t,u,cherry):
    pr=priority(t,u)
    if not pr['excluded_2a_to_2d']: return {'admitted':False,'reason':'Figure16 earlier source priority','priority':pr}
    source=Graph(u); path=set(source.path(*(source.labels[x] for x in cherry)))
    pendant=[e for e in source.edges if e[0] in path and e[1] not in path]
    assert len(pendant)==2
    rawblocks=source.cut_partition(pendant)
    assert len(rawblocks)==3
    red=tidy(t,[source.restrict(b) for b in rawblocks])
    if len(red['sources'])!=3: return {'admitted':False,'reason':'not three live','priority':pr,'reduced':red}
    state=earlier(red['target'],red['sources']); g=Graph(red['target'])
    es=[span_edges(g,b) for b in red['blocks']]
    common=set.intersection(*es)
    overlap={(i,j):es[i]&es[j] for i in range(3) for j in range(i+1,3) if es[i]&es[j]}
    return {'admitted':True,'priority':pr,'pendant_cuts':thaw(pendant),'rawblocks':thaw(rawblocks),'reduced':red,'earlier':state,'common':thaw(sorted(common)),'edge_overlap':{str(k):thaw(sorted(v)) for k,v in overlap.items()}}
def separators(tree,far):
    g=Graph(tree); y=set(far)&set(g.labels); z=set(g.labels)-y
    if not y or not z: return [{'partition':[sorted(g.labels)],'paid':0,'cuts':[]}]
    terminal=[]; seen=set()
    for d in range(1,len(g.labels)):
        for cuts in itertools.combinations(sorted(g.edges),d):
            p=g.cut_partition(cuts)
            if len(p)!=d+1 or p in seen or any(set(b)&y and set(b)&z for b in p): continue
            seen.add(p)
            if any(refines(p,r['partition']) for r in terminal): continue
            terminal.append({'partition':thaw(p),'paid':d,'cuts':thaw(cuts)})
    return terminal
def constraints(t,forest,constraints):
    g=Graph(t); states=[{'per_source':[[sorted(Graph(f).labels)] for f in forest],'paid':0,'stages':[]}]
    for color,edge in constraints:
        far=g.descendant_labels(edge[1]); out=[]
        for state in states:
            evolving=[state]
            for block in state['per_source'][color]:
                if not set(block)&far or not set(block)-far: continue
                stage_tree=Graph(forest[color]).restrict(block)
                cuts=separators(stage_tree,far)
                updated=[]
                for prev in evolving:
                    for cut in cuts:
                        parts=[list(map(list,x)) for x in prev['per_source']]
                        parts[color]=[b for b in parts[color] if b!=block]+cut['partition']
                        updated.append({'per_source':parts,'paid':prev['paid']+cut['paid'],'stages':prev['stages']+[{'source':color,'old':block,'tree':thaw(stage_tree),'target_edge':thaw(edge),**cut}]})
                evolving=updated
            out.extend(evolving)
        states=out
    for state in states:
        state['blocks']=thaw(cp([b for x in state['per_source'] for b in x]))
        assert state['paid']==len(state['blocks'])-len(forest)
    return states
def chain_rows(red):
    t,forest,blocks=red['target'],red['sources'],red['blocks']; g=Graph(t)
    spans=[g.span(b) for b in blocks]; es=[span_edges(g,b) for b in blocks]
    pairs=[(i,j) for i in range(3) for j in range(i) if es[i]&es[j]]
    if len(pairs)!=2: return None
    middle=set(pairs[0])&set(pairs[1]); assert len(middle)==1
    b=next(iter(middle)); a,c=[i for i in range(3) if i!=b]
    if spans[a]&spans[c]: return None
    rows=[]
    for e,f in itertools.product(sorted(es[a]&es[b]),sorted(es[c]&es[b])):
        branches=[]
        for name,cons in [('AB',[(b,e),(c,f)]),('AC',[(b,e),(b,f)]),('BB',[(a,e),(c,f)]),('BC',[(a,e),(b,f)])]:
            branches.extend(dict(assignment=name,**s) for s in constraints(t,forest,cons))
        unique={cp(x['blocks']):x for x in branches}
        minimal=[x for x in unique.values() if not any(y['paid']<x['paid'] and refines(x['blocks'],y['blocks']) for y in unique.values())]
        vector=[1,1,*[2+x['paid'] for x in minimal]]
        rows.append({'edges':[thaw(e),thaw(f)],'endpoint_indices':[a,c],'middle':b,'children':minimal,'vector':vector,'mass':str(sum((BASE**(-q) for q in vector),Fraction()))})
    return rows
def reconstruct(parent_t,parent_u,prepared,opt):
    red=prepared['reduced']; rows=[]
    for p in opt['optimal']:
        full=[sorted(z for x in b for z in red['expansion'][x]) for b in p]+red['closed']
        assert valid(parent_t,parent_u,full)[0]
        assert refines(full,prepared['rawblocks'])
        rows.append(full)
    return rows
def main():
    common=json.loads((HERE.parent/'joint_macro/COMMON-PIN-v2.json').read_text())
    start=time.perf_counter(); p=prepare(common['T'],common['Tprime'],common['cherry'])
    assert p['admitted'] and p['common'] and not p['earlier']['rule6'] and not p['earlier']['rule7']
    red=p['reduced']; e=p['common'][0]; rows=[]
    for keep in range(3):
        cons=[(i,e) for i in range(3) if i!=keep]
        rows.extend(dict(survivor=keep,**s) for s in constraints(red['target'],red['sources'],cons))
    opt=exact_forest(red['target'],red['sources']); assert opt['residual']==3
    for s in rows:
        fs=[Graph(f).restrict(b) for f,bs in zip(red['sources'],s['per_source']) for b in bs]
        sub=exact_forest(red['target'],fs)
        s['exact_residual']=sub['residual'];s['total_residual']=s['paid']+sub['residual'];s['optimal']=sub['optimal']
    vector=[1,1,*[2+s['paid'] for s in rows]]
    assert vector==[1,1,4,4,4] and min(x['total_residual'] for x in rows)==3
    fullmass=str(sum((BASE**(-q) for q in vector),Fraction())); assert fullmass=='921759400/949132107'
    common_receipt={'prepared':p,'exact':opt,'expanded_original_witnesses':reconstruct(common['T'],common['Tprime'],p,opt),'children':rows,'vector':vector,'mass':fullmass,'seconds':time.perf_counter()-start}
    write('algorithm-review-macro-common-n8.json',common_receipt)
    write('algorithm-review-macro-pilot.json',{'n8_seconds':time.perf_counter()-start,'family_projection':'measure one deletion score before256 family; no n11 exact census'})
    source=json.loads((HERE.parent/'joint_macro/CHAIN-PIN-v3.json').read_text())
    labels=sorted(Graph(source['T']).labels); scored=[]; admitted=[]
    before=time.perf_counter()
    for n in range(7,12):
        for others in itertools.combinations([x for x in labels if x not in [9,10]],n-2):
            selected=sorted([9,10,*others]); t=thaw(Graph(source['T']).restrict(selected)); u=thaw(Graph(source['Tprime']).restrict(selected))
            prep=prepare(t,u,[9,10]); row={'labels':selected,'n':n,'T':t,'Tprime':u,'prepared':prep}
            if prep['admitted'] and not prep['earlier']['rule6'] and not prep['earlier']['rule7']:
                chains=chain_rows(prep['reduced'])
                if chains is not None:
                    row['chain_rows']=chains; row['eligible_chain']=True; row['all_mass_fail']=all(Fraction(x['mass'])>1 for x in chains); admitted.append(row)
            scored.append(row)
            if len(scored)==1: write('algorithm-review-macro-deletion-pilot.json',{'first_score_seconds':time.perf_counter()-before,'projection_256_seconds':256*(time.perf_counter()-before),'assumption':'linear per admission score, actual denominator retained; exact optima only on refuter'})
    assert len(scored)==256
    assert len(admitted)==2 and all(x['all_mass_fail'] for x in admitted)
    smallest=min(admitted,key=lambda r:r['n']); assert smallest['n']==10
    red=smallest['prepared']['reduced']; opt=exact_forest(red['target'],red['sources'])
    assert opt['residual']==2 and [cp(p) for p in opt['optimal']]==[cp([[1,3,5,7],[2],[4],[6],[8,9]])]
    for row in smallest['chain_rows']:
        assert row['vector']==[1,1,4,4,4,4] and row['mass']=='2865278200/2847396321'
        for child in row['children']:
            fs=[Graph(f).restrict(b) for f,bs in zip(red['sources'],child['per_source']) for b in bs]
            sub=exact_forest(red['target'],fs); child['exact_residual']=sub['residual'];child['total']=child['paid']+sub['residual'];child['optimal']=sub['optimal']
            assert all(valid_forest(red['target'],red['sources'],p) for p in sub['optimal'])
        assert min(x['total'] for x in row['children'])==2
        bad=[x for x in row['children'] if x['assignment']!='BB']
        assert bad and min(x['total'] for x in bad)==3
        assert not any(refines(opt['optimal'][0],x['blocks']) for x in bad)
        row['missing_BB_copy']={'nonempty_children':len(bad),'best_total':3,'clean_best_total':2,'lost_unique_optimum':opt['optimal'][0],'false_optimum_comparator_caught':True}
    smallest['exact_current_forest']=opt
    smallest['expanded_original_witnesses']=reconstruct(smallest['T'],smallest['Tprime'],smallest['prepared'],opt)
    write('algorithm-review-macro-deletion-family.json',{'tested':256,'eligible_chains':2,'refuters':2,'seconds':time.perf_counter()-before,'scope':'smallest eligible refuter in pinned deletions only','rows':scored,'smallest':smallest})
    print(json.dumps({'n8_common_mass':fullmass,'common_residual':3,'deletions':256,'eligible_chains':2,'smallest_n':10,'chain_residual':2,'missing_BB_caught':len(smallest['chain_rows'])}))
if __name__=='__main__': main()
