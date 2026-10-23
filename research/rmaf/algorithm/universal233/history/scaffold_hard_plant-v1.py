"""One-shot controlled hard-subtree stress for the actual remaining scaffold.
No large optimum search: local six-label optimum is an existing DEV fixture.
"""
from scaffold_vertex_replay import *


def substitute(t,mapping):
    return mapping.get(t,t) if isinstance(t,int) else [substitute(t[0],mapping),substitute(t[1],mapping)]


def relabel(t,mapping):
    return mapping[t] if isinstance(t,int) else [relabel(t[0],mapping),relabel(t[1],mapping)]

if __name__=='__main__':
    start=time.perf_counter();ctls=controls();pin=json.loads((HERE/'SCAFFOLD-HARD-PLANT-PIN-v1.json').read_text());local=json.loads((ROOT/'results/algorithm-universal233-hard-plant-local-v1.json').read_text())
    assert local['minimum_cuts']==2 and local['partitions_tested']==203
    assert all(a['excluded_2a_to_2d'] for a in local['admission_both_orientations'])
    maps={0:dict(zip(range(6),[0,9,10,11,12,13])),2:dict(zip(range(6),[2,14,15,16,17,18]))}
    ts={k:relabel(local['T'],m) for k,m in maps.items()};ss={k:relabel(local['Tprime'],m) for k,m in maps.items()}
    for k in ts:assert Tree(ts[k]).clusters(Tree(ts[k]).labels)!=Tree(ss[k]).clusters(Tree(ss[k]).labels)
    sk=pin['skeleton'];t=substitute(sk['original_T'],ts);s=substitute(sk['original_Tprime'],ss);ch=sk['selected_cherry']
    assert selected_valid(t,s,ch),'plant failed actual complete source admission'
    w=scan_child(t,s,ch);assert w is not None
    o=run_vertex(w)
    out={'controls':ctls,'plant_local_clean_twin':True,'actual_admission':[applicability(Tree(t),Tree(s)),applicability(Tree(s),Tree(t))],'replay':o,'elapsed_seconds':time.perf_counter()-start,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'pin_sha256':hashlib.sha256((HERE/'SCAFFOLD-HARD-PLANT-PIN-v1.json').read_bytes()).hexdigest(),'scope':'Exact finite development stress. Post-pretest fire is not full algorithm refutation; later paid decomposition budgets printed.'}
    (ROOT/'results/algorithm-universal233-scaffold-hard-plant-v1.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Actual19-label source admission PASS; exact local2-cut plant used, no19-label exhaustive optimum search.')
    for r in o['vertex_rows']:print('v',r['vertex'],'regions',r['region_counts'],'raw',r['raw_full_mass'],'depth1',r['after_depth1_full_mass'],'paid',r['after_one_paid_continuation_full_mass'])
    print('elapsed',out['elapsed_seconds'])
