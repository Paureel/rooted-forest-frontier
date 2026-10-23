"""Cross-replay one frozen edge-route witness with the earlier raw-cut checker.
This author wrote the earlier checker; this is cross-implementation evidence,
not the required fresh-nonauthor review. No edge-route checker code is imported.
"""
import hashlib,json,pathlib,sys,types
BASE=pathlib.Path('/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf')
HERE=BASE/'thesis_correctness/repair';sys.path.insert(0,str(HERE.parent))
from local_obligations import component_data,info,controls

def graph(record):
    ps={int(k):v for k,v in record['parent'].items()}
    children={v:[] for v in ps}
    for v,p in ps.items():
        if p is not None:children[int(p)].append(v)
    labels={int(k):frozenset([v]) for k,v in record['labels'].items()}
    return types.SimpleNamespace(child=children,label=labels)

def af(blocks,source,target):
    used=set()
    for b in blocks:
        shape,vertices=info(source,b);targetshape,_=info(target,b)
        if shape is None or shape!=targetshape or used&vertices:return False
        used|=vertices
    return True

def named(blocks):return sorted([sorted(next(iter(x)) for x in b) for b in blocks])
def main():
    fixed,_=controls()
    p=HERE/'edge_route/first-reached-root-witness.json';d=json.loads(p.read_text())
    graphs={k:graph(d[k]) for k in ['T1','T2','F1','F2']}
    e=set(d['E']);normalized=set(d['normalized_E']);f2=graphs['F2']
    before=component_data(f2,e);after=component_data(f2,normalized)
    checks={'fixed_controls':len(fixed),'original_blocks_exact':named(before)==sorted(d['original_blocks']),'normalized_blocks_exact':named(after)==sorted(d['normalized_blocks']),'absent_lca_parent':d['F2']['parent'][str(d['LCA'])] is None,'path_removed_exact':e&set(d['path'])==set(d['removed_path_edges']),'root_rule_exact':normalized==e-set(d['removed_path_edges']),'cut_drop_exact':len(e)-len(normalized)==2}
    for k in ['T1','T2','F1']:
        checks['original_af_'+k]=af(before,graphs[k],f2)
        checks['normalized_af_'+k]=af(after,graphs[k],f2)
    uncut=component_data(f2,set())
    checks['corruption_missing_pendant_cut_caught']=not af(uncut,graphs['T1'],f2)
    assert all(v is True for k,v in checks.items() if k!='fixed_controls'),checks
    out={'status':'passed-cross-implementation','checks':checks,'before_blocks':named(before),'after_blocks':named(after),'provenance':'Uses earlier same-author raw-deletion evaluator; no edge-route checker code. Not fresh-nonauthor review. Does not replay generator history.','witness_path':str(p),'witness_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'checker_path':str(HERE.parent/'local_obligations.py'),'checker_sha256':hashlib.sha256((HERE.parent/'local_obligations.py').read_bytes()).hexdigest()}
    target=BASE/'results/thesis-correctness-repair-root-cross-replay.json';target.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'checks':len(checks)-1,'all_passed':True,'receipt':str(target)}))
if __name__=='__main__':main()
