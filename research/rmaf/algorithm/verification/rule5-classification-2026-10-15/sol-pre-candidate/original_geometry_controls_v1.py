#!/usr/bin/env python3
"""One-shot original-hull/attachment/split controls on the already fixed bank."""
import importlib.util
import json
from pathlib import Path
import sys
import time
HERE=Path(__file__).resolve().parent
spec=json.loads((HERE/'ORIGINAL-GEOMETRY-EXPECTATIONS-v1.json').read_text())
inputs=json.loads((HERE/'FIXTURE-INPUTS-v1.json').read_text())
ms=importlib.util.spec_from_file_location('own_BFS_geometry',HERE/'reused/graph_partition_v2.py')
old=importlib.util.module_from_spec(ms);ms.loader.exec_module(old)
Graph,State=old.Graph,old.State
mode=sys.argv[1];result={'candidate_contact':False,'context':spec['context'],'mode':mode,'cases':[],'splits':[],'false_twins':[]}
start=time.perf_counter()


def at(t,address):
    for bit in address:t=t[bit]
    return t
def cherries(g):return [(v,g.at[v+(0,)],g.at[v+(1,)]) for v in g.adj if v+(0,) in g.at and v+(1,) in g.at]
def root_component(g,cs):
    banned={frozenset([tuple(c),tuple(c)[:-1]]) for c in cs};seen={()};todo=[()]
    for v in todo:
        for w in g.adj[v]:
            if w not in seen and frozenset([v,w]) not in banned:seen.add(w);todo.append(w)
    return seen,sorted(g.at[v] for v in seen if v in g.at)
def hull_split(g,F,cs):
    banned={frozenset([tuple(c),tuple(c)[:-1]]) for c in cs};fragments=[];records=[]
    for B in F:
        hull=set(g.hull(B));seen=set();pieces=[];empty=[]
        for first in sorted(hull):
            if first in seen:continue
            todo=[first];piece=set()
            for v in todo:
                if v in seen:continue
                seen.add(v);piece.add(v)
                todo.extend(w for w in g.adj[v] if w in hull and w not in seen and frozenset([v,w]) not in banned)
            labels=sorted(g.at[v] for v in piece if v in g.at and g.at[v] in B)
            if labels:pieces.append(labels);fragments.append(labels)
            else:empty.append([list(v) for v in sorted(piece)])
        records.append({'B':B,'originalHull':[list(v) for v in sorted(hull)],'fragments':pieces,'empty_hull_pieces':empty})
    return fragments,records
def key(F):return sorted(sorted(B) for B in F)
def same(a,b):assert a==b
def caught(name,call):
    try:call()
    except AssertionError:result['false_twins'].append({'name':name,'caught':True})
    else:raise AssertionError('surviving original-geometry false twin '+name)


try:
    assert mode in ('pilot','full')
    cases=[c for c in inputs['cases'] if c['id']=='sizeTwo7'] if mode=='pilot' else inputs['cases']
    for c in cases:
        t,s=Graph(c['target']),Graph(c['source'])
        root_vertices,root_labels=root_component(t,c['target_attachments'])
        assert root_labels==spec['target_root_remainders'][c['id']]
        assert () in root_vertices and root_labels
        source_root_vertices,source_root_labels=root_component(s,c['original_cuts'])
        assert source_root_labels==sorted(c['partition'][-1])
        hull=s.hull([c['a'],c['b']]);lca=min(hull,key=len)
        proper_ancestors=[lca[:i] for i in range(len(lca))]
        assert proper_ancestors and all(v in source_root_vertices for v in proper_ancestors)
        row={'id':c['id'],'target_root_labels':root_labels,'source_root_labels':source_root_labels,
             'source_selected_LCA':list(lca),'source_original_ancestors_retained':[list(v) for v in proper_ancestors]}
        if c['id'] in spec['good_source_pendant_cherries']:
            x=Graph(at(c['source'],c['original_cuts'][0]))
            cat=all(sum(w in x.adj and w not in x.at for w in [v+(0,),v+(1,)])<=1 for v in x.adj)
            cc=cherries(x);assert cat and len(cc)==spec['good_source_pendant_cherries'][c['id']]==1
            assert t.topology(c['partition'][0])==s.topology(c['partition'][0])
            row.update({'actual_source_subtree':x.tree,'caterpillar':cat,'cherries':[list(v) for v,_,_ in cc]})
        else:
            core=Graph(s.restriction(c['partition'][-1]));cc=cherries(core)
            second=[(v,a,b) for v,a,b in cherries(s) if {a,b}=={c['p'],c['q']}]
            assert len(cc)==2 and len(second)==1 and list(second[0][0])==spec['outside_second_cherry_original_parent']
            row.update({'restricted_core_cherries':[[a,b] for _,a,b in cc],'second_original_source_parent':list(second[0][0])})
        result['cases'].append(row)
    if mode=='full':
        c=next(c for c in cases if c['id']=='large8');t,s=Graph(c['target']),Graph(c['source'])
        for name in ['large_crossing','large_no_crossing']:
            e=inputs['controls'][name];expected=spec[name]
            fragments,occupancy=hull_split(t,e['F'],c['target_attachments'])
            assert len(e['F'])==expected['old_blocks'] and len(fragments)==expected['split_blocks']
            assert len(fragments)-len(e['F'])==expected['added']<=2
            assert State(c['target'],[c['source']]).agrees(fragments)
            X=set(c['partition'][0]);regrouped=[B for B in fragments if not set(B)<=X]+[sorted(X)]
            assert key(regrouped)==key(e['G']) and len(regrouped)==expected['after_regroup']
            assert len(fragments)-len(regrouped)==expected['saved']==2
            result['splits'].append({'id':name,'original_hull_occupancy':occupancy,'split':fragments,
                                    'regrouped':regrouped,'added':expected['added'],'saved':expected['saved']})
        crossing=inputs['controls']['large_crossing']['F'][0];h=t.hull(crossing)
        suppressed={v for v in h if v in t.at or sum(w in h for w in t.adj[v])!=2}
        assert suppressed!=set(h)
        caught('suppressed_original_hull',lambda:same(suppressed,set(h)))
        caught('wrong_no_crossing_split_increment',lambda:same(result['splits'][1]['added'],2))
        caught('wrong_regroup_saving',lambda:same(result['splits'][0]['saved'],1))
        caught('omitted_root_taxon',lambda:same(result['cases'][0]['target_root_labels'],[2,3]))
        assert {r['name'] for r in result['false_twins']}==set(spec['false_twins'])
    result['passed']=True
except Exception as exc:
    result['passed']=False;result['failure']=repr(exc);raise
finally:
    result['seconds']=time.perf_counter()-start
    (HERE/('original-geometry-'+mode+'-v1.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':True,'mode':mode,'cases':len(result['cases']),'splits':len(result['splits']),'false_twins':len(result['false_twins']),'seconds':result['seconds']}))
