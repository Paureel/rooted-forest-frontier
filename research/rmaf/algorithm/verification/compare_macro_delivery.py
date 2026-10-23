"""Compare every emitted frozen development child against fresh graph receipt."""
import copy,json
from pathlib import Path
from independent_graph import Graph,exact_forest,thaw
from review_macro import cp,refines
HERE=Path(__file__).resolve().parent; CAMPAIGN=HERE.parents[1]; OUT=CAMPAIGN/'results'
def edge(g,e):
    numeric=tuple(g.address[x] for x in e)
    assert numeric in g.edges
    return numeric
def far(g,e): return tuple(sorted(g.descendant_labels(e[1])))
common=json.loads((OUT/'algorithm-macro-joint-pilot-v2.json').read_text())['fixture']
fresh=json.loads((OUT/'algorithm-review-macro-common-n8.json').read_text())
assert {cp(x['blocks']) for x in common['joint_macro']['children']}=={cp(x['blocks']) for x in fresh['children']}
commons=[]
for child in common['joint_macro']['children']:
    actual=[]
    for i,forest in enumerate(common['reduced']['forest_trees']):
        g=Graph(forest); raw=child['cuts_by_source'].get(str(i),[])
        cuts=[edge(g,e) for e in raw]
        actual.extend(g.cut_partition(cuts))
    assert cp(actual)==cp(child['blocks'])
    assert child['paid']==len(actual)-3
    f=next(x for x in fresh['children'] if cp(x['blocks'])==cp(child['blocks']))
    assert child['total_residual']==f['total_residual'] and child['paid']==f['paid']
    commons.append({'blocks':child['blocks'],'actual_paid':child['paid'],'exact_total_residual':f['total_residual'],'pass':True})
delivery=json.loads((OUT/'algorithm-macro-chain-minimize-v2.json').read_text())['smallest_refuter_exact_replay']
fresh=json.loads((OUT/'algorithm-review-macro-deletion-family.json').read_text())['smallest']
gt=Graph(delivery['fixture']['reduced']['T']); gi=Graph(fresh['prepared']['reduced']['target'])
rows=[]; copies=[]
for row in delivery['edge_pairs']:
    key=(far(gt,edge(gt,row['AB_edge'])),far(gt,edge(gt,row['BC_edge'])))
    independent=next(r for r in fresh['chain_rows'] if tuple(far(gi,e) for e in r['edges'])==key)
    assert {cp(x['blocks']) for x in row['children']}=={cp(x['blocks']) for x in independent['children']}
    stages=0
    for child in row['children']:
        total=0
        for stage in child['stages']:
            g=Graph(stage['old_tree']); cuts=[edge(g,e) for e in stage['cut_edges']]
            assert cp(g.cut_partition(cuts))==cp(stage['new_blocks'])
            total+=len(cuts); stages+=1
        assert total==child['paid']==len(child['blocks'])-3
        freshchild=next(c for c in independent['children'] if cp(c['blocks'])==cp(child['blocks']))
        assert child['total_residual']==freshchild['total']
    mutant=copy.deepcopy(row)
    mutant['children']=[x for x in mutant['children'] if x['assignment']!='BB']
    assert mutant['children'] and min(x['total_residual'] for x in mutant['children'])==3
    assert not any(refines(fresh['exact_current_forest']['optimal'][0],x['blocks']) for x in mutant['children'])
    copies.append(mutant)
    rows.append({'target_edge_far_sets':key,'children':len(row['children']),'source_stages_checked':stages,'paid_vector':row['paid_vector'],'full_vector':row['full_vector'],'independent_mass':independent['mass'],'missing_BB_caught':True,'pass':True})
(HERE/'COPY-macro-missing-BB.json').write_text(json.dumps(copies,indent=2)+'\n')
(OUT/'algorithm-review-macro-actual-emission-check.json').write_text(json.dumps({'common_children':commons,'chain_edge_pairs':rows,'actual_stage_cut_checks':sum(x['source_stages_checked'] for x in rows),'scope':'delivered development entry output and source-stage realization, not total A0 executor'},indent=2)+'\n')
print(json.dumps({'common_children_checked':len(commons),'chain_edge_pairs':len(rows),'source_stage_cut_checks':sum(x['source_stages_checked'] for x in rows),'actual_BB_copy_catches':len(copies)}))
