"""One-shot actual vertex-selector and paid continuation replay.
Core coverage and source rule7/decomposition graph imports remain conditional.
All concrete generated child costs and local pretests below are executed.
"""
from scaffold_augment import *


def region_colors(t,v,labels):
    assert v not in t.leaf.values();graph={w:set() for w in t.child}
    for a,b in t.edges:graph[a].add(b);graph[b].add(a)
    todo=set(graph)-{v};color={};k=0
    while todo:
      seed=min(todo);seen={seed};stack=[seed]
      while stack:
        a=stack.pop()
        for b in graph[a]-seen-{v}:seen.add(b);stack.append(b)
      todo-=seen;ls=[x for x in labels if t.leaf[x] in seen]
      if ls:
        for x in ls:color[x]=k
        k+=1
    assert set(color)==set(labels)
    return color


def emission_states(raw,forest,pair,v):
    t=Tree(raw);out=[]
    for i in pair:
      src=Tree(forest[i]);co=region_colors(t,v,src.labels)
      assert 2<=len(set(co.values()))<=3
      gen=generate(forest[i],co)
      for k in gen['cores']:
        f=[ft for j,ft in enumerate(forest) if j!=i]+[src.restriction(b) for b in k['partition']]
        r=tidy(raw,f)
        out.append({'source':i,'colors':co,'cost':k['cost'],'cuts':k['cuts'],'partition':k['partition'],'reduced':r,'depth1':depth1(r['T'],r['forest_trees']),'classification':classify(r['T'],r['forest_trees'])})
    return out


def paid_next(raw,forest,c):
    done=depth1(raw,forest)
    if done is not None:return Fraction(0),{'kind':'exact_depth1','value':done}
    cl=classify(raw,forest)
    if cl['overlap_pairs']:
      # Fully generated ONE further paid split. Any recursive descendants are
      # charged at full remaining budget; no unexecuted terminal bonus taken.
      pair=cl['overlap_pairs'][0];t=Tree(raw);v=min(t.span(cl['blocks'][pair[0]])&t.span(cl['blocks'][pair[1]]))
      es=emission_states(raw,forest,pair,v);mass=sum(c**(-e['cost']) for e in es)
      return mass,{'kind':'one_actual_vertex_split','pair':pair,'vertex':v,'decreases':[e['cost'] for e in es],'mass':str(mass)}
    pre=[]
    for ft in forest:
      f=Tree(ft);local=depth1(Tree(raw).restriction(f.labels),[ft]);pre.append(local)
    lower=[2 if x is None else x for x in pre];calls=[sum(x for j,x in enumerate(lower) if j!=i) for i,x in enumerate(pre) if x is None]
    mass=sum(c**(-d) for d in calls)
    return mass,{'kind':'actual_disjoint_depth1_schedule','pretest_values':pre,'other_parent_lower_bound_losses':calls,'mass':str(mass)}


def run_vertex(w):
    start=time.perf_counter();r=w['reduced'];raw,forest=r['T'],r['forest_trees'];cl=classify(raw,forest);assert len(cl['overlap_pairs'])==1
    pair=cl['overlap_pairs'][0];t=Tree(raw);vertices=sorted(t.span(cl['blocks'][pair[0]])&t.span(cl['blocks'][pair[1]]));c=Fraction(233,100);rows=[]
    for v in vertices:
      es=emission_states(raw,forest,pair,v);rawmass=sum(c**(-e['cost']) for e in es);live=sum(c**(-e['cost']) for e in es if e['depth1'] is None);paid=Fraction(0)
      for e in es:
        m,receipt=paid_next(e['reduced']['T'],e['reduced']['forest_trees'],c);paid+=c**(-e['cost'])*m;e['continuation']=receipt
      rows.append({'vertex':v,'region_counts':[len(set(region_colors(t,v,Tree(forest[i]).labels).values())) for i in pair],'emissions':es,'raw_full_mass':str(2/c+rawmass/c**2),'after_depth1_full_mass':str(2/c+live/c**2),'after_one_paid_continuation_full_mass':str(2/c+paid/c**2)})
    return {'original_T':w['original_T'],'original_Tprime':w['original_Tprime'],'cherry':w['cherry'],'reduced':r,'vertex_rows':rows,'minimum_raw_full_mass':str(min(Fraction(r['raw_full_mass']) for r in rows)),'minimum_depth1_full_mass':str(min(Fraction(r['after_depth1_full_mass']) for r in rows)),'minimum_one_paid_full_mass':str(min(Fraction(r['after_one_paid_continuation_full_mass']) for r in rows)),'elapsed_seconds':time.perf_counter()-start,'scope':'Actual finite emitted costs/pretests. Universal source-core cover and decomposition interfaces remain OPEN; no whole-algorithm bound.'}

if __name__=='__main__':
    ctl=controls();g=json.loads((ROOT/'results/algorithm-universal233-scaffold-greedy-v1.json').read_text());w=g['stages'][-1]['best']['state'];o=run_vertex(w)
    out={'controls':ctl,'replay':o,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};(ROOT/'results/algorithm-universal233-scaffold-vertex-replay-v1.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in o.items() if k not in ['vertex_rows','reduced','original_T','original_Tprime']}))
    for r in o['vertex_rows']:print('v',r['vertex'],'r',r['region_counts'],'raw',r['raw_full_mass'],'depth1',r['after_depth1_full_mass'],'paid',r['after_one_paid_continuation_full_mass'])
