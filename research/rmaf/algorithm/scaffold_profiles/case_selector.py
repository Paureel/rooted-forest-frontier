"""One-shot DEVELOPMENT selector and capped raw-profile classifier.
Uses completed controlled graph/core primitives; not independent verification.
"""
from pathlib import Path
from collections import Counter
import sys,json,hashlib
sys.path.insert(0,str(Path(__file__).resolve().parent))
import continuation_probe as D
C=D.C;O=D.O;R=D.ROOT

def capped_profile(raw,color,cap=4):
    t=C.read_source(raw,color);n=len(C.groups(t));emissions=[];visits=0
    def walk(t,cuts):
        nonlocal visits
        if len(emissions)>=cap:return
        visits+=1;t,_=C.normalize(t,color);gs=C.groups(t);used={color[g.group[0]] for g in gs}
        if len(used)==1:
            emissions.append(len(cuts));return
        assert len(used)==2
        counts=Counter(color[g.group[0]] for g in gs)
        unique=sorted(a for a,v in counts.items() if v==1)
        selected=[next(g for g in gs if color[g.group[0]]==unique[0])] if unique else list(C.mixed_cherry(t))
        for g in selected:
            if len(emissions)>=cap:break
            assert g.address and g.address not in cuts
            rest,_=C.delete_group(t,g.address);assert rest is not None
            walk(rest,cuts+[g.address])
    walk(t,[])
    assert visits<=cap*n
    return {'class':len(emissions),'complete':len(emissions)<cap,'prefix_costs':emissions,'prefix_visits':visits,'initial_groups':n}

def select(target,A,B):
    t=O.Tree(target);ha,hb=t.span(A),t.span(B);shared=ha&hb
    if not shared:raise ValueError('outside overlapping-pair case')
    candidates=[]
    for v in sorted(shared,key=lambda v:(len(v),v)):
        colors=[]
        for S in (A,B):
            col={x:int(t.leaf[x][len(v)])+1 if t.leaf[x].startswith(v) else 0 for x in S}
            gs=[[x for x,a in col.items() if a==s] for s in sorted(set(col.values()))]
            colors.append(gs)
        assert all(2<=len(gs)<=3 for gs in colors)
        if any(len(gs)==3 for gs in colors):
            return {'case':'three-region','vertex':v,'color_groups':colors}
        mutual=all(not t.span(g)&hb for g in colors[0]) and all(not t.span(g)&ha for g in colors[1])
        candidates.append({'case':'mutually-clear-binary','vertex':v,'color_groups':colors,'checked_mutual_clear':mutual})
    # Exchange uses an actual oriented target edge, never arbitrary color sets.
    for edge in t.edges:
        if not (edge[0] in shared and edge[1] in shared):continue
        descendants=set(t.below[edge[1]])
        groups=[[sorted(set(S)&descendants),sorted(set(S)-descendants)] for S in (A,B)]
        assert all(all(g for g in parent) for parent in groups)
        mutual=all(not t.span(g)&hb for g in groups[0]) and all(not t.span(g)&ha for g in groups[1])
        if mutual:return {'case':'mutually-clear-binary','vertex':edge[0],'target_edge':list(edge),
                          'target_descendant_labels':sorted(descendants),'color_groups':groups,'checked_mutual_clear':True}
    raise AssertionError(('OPEN selector lemma fired',target,sorted(A),sorted(B),candidates))

def main():
    out=R/'research/rmaf/results/algorithm-scaffold-profiles-selector-v2.json'
    if out.exists():raise FileExistsError(out)
    assert select(((0,2),(1,3)),{0,1},{2,3})['case']=='mutually-clear-binary'
    assert select(((0,3),(1,(2,4))),{0,1,2},{3,4})['case']=='three-region'
    caught=False
    try:select(((0,1),(2,3)),{0,1},{2,3})
    except ValueError:caught=True
    assert caught
    literal=[(((0,1),2),{0:0,1:0,2:1}),(((0,1),(2,3)),{i:i%2 for i in range(4)}),(((0,1),(2,(3,4))),{0:0,1:1,2:0,3:0,4:1}),((((0,1),(2,3)),(4,5)),{i:i%2 for i in range(6)})]
    controls=[]
    for t,col in literal:
        actual=C.generate(t,col);expected=min(4,len(actual['raw_cores']));cap=capped_profile(t,col)
        assert cap['class']==expected
        controls.append({'raw_profile':sorted(e['cost'] for e in actual['raw_cores']),'capped':cap})
    assert controls[-1]['capped']['class']==4
    assert min(3,len(C.generate(*literal[-1])['raw_cores']))!=4
    rows=[]
    for file in ('algorithm-scaffold-profiles-continuation-pilot-v1.json','algorithm-scaffold-profiles-continuation-extension-v1.json'):
      for row in json.loads((R/'research/rmaf/results'/file).read_text())['rows']:
        t,fs,spans,ov,good,cc=D.geometry(row['initial']['T'],row['initial']['forest_trees']);i,j=ov[0]
        selector=select(t.raw,fs[i].labels,fs[j].labels);caps=[]
        for s in row['selectors']:
          for b in s['branches']:
            if len(set(b['colors'].values()))!=2:continue
            col={int(x):v for x,v in b['colors'].items()};cp=capped_profile(fs[b['parent']].raw,col)
            assert cp['class']==min(4,len(b['raw_profile']))
            caps.append({'vertex':s['target_vertex'],'parent':b['parent'],'capped':cp})
        rows.append({'n':row['n'],'selector':selector,'classifications':caps})
    result={'scope':'DEVELOPMENT fixed-control selector/capped-classifier checks; universal graph/source/rank claims OPEN','controls':controls,'disjoint_refusal':caught,'false_three_cap_caught':True,'rows':rows,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'rows':[(x['n'],x['selector']['case'],x['selector']['vertex']) for x in rows],'literal_control_classes':[x['capped']['class'] for x in controls],'out':str(out)}))
if __name__=='__main__':main()
