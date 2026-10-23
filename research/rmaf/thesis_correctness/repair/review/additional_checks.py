"""One-shot source consumer controls using only the fresh review evaluator."""
from fresh_exact import *
from hunt import fragment, normal
import re

def replace(x,m):
    return m.get(x,x) if isinstance(x,str) else [replace(y,m) for y in x]

def check_two_stage():
    f=json.loads((REPAIR/'two-stage-original-spec.json').read_text());rows=[]
    for compound in [False,True]:
        mapping={v:[v+'1',v+'2'] for v in ['a','c','x']} if compound else {}
        a,b=Tree(replace(f['t1'],mapping)),Tree(replace(f['t2'],mapping))
        endpoint=lambda v:b.edge_for[frozenset(mapping.get(v,[v]))]
        u=b.lca([endpoint('a'),endpoint('c')]);p=b.parent[u];P={endpoint('b1'),endpoint('b2')}
        for selected in f['positive_cutsets']:
            e={endpoint(v) for v in selected};opt,mins=optimum(a,b)
            c1=normal(b,e|P,b.path_edges(endpoint('a'),endpoint('c')),u,set())
            c2=normal(b,c1,b.path_edges(endpoint('x'),u),b.lca([endpoint('x'),u]),set())
            row={'compound':compound,'selected':selected,'optimum':opt,'original_count':len(e),'first_count':len(c1),'second_count':len(c2),
                 'original_AF':af(a,b,e),'first_AF':af(a,b,c1),'second_AF':af(a,b,c2),
                 'second_path_original_clusters':[sorted(b.cluster[v]) for v in sorted(b.path_edges(endpoint('x'),u))],
                 'first_u_fragment':sorted(fragment(b,u,c1)),'first_x_fragment':sorted(fragment(b,endpoint('x'),c1)),
                 'final_cuts':[sorted(b.cluster[v]) for v in sorted(c2)],'required_cut_deletion_AF':[af(a,b,c2-{v}) for v in sorted(P)]}
            assert opt==f['expected_optimum']==len(e)
            assert c2==P and all(row[k] for k in ['original_AF','first_AF','second_AF'])
            assert not any(row['required_cut_deletion_AF'])
            assert fragment(b,u,c1) and fragment(b,endpoint('x'),c1)
            rows.append(row)
    return rows

rows=check_two_stage()
res={'status':'passed','two_stage_cases':rows,'scope':'Two frozen original-edge cutsets and their intact-common-compound expansions; finite controls only. Suppression transport not proved.'}
(ROOT/'results/thesis-correctness-repair-review-two-stage.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({'status':res['status'],'cases':len(rows),'negative_AF_deletions_rejected':sum(len(r['required_cut_deletion_AF']) for r in rows)}))
