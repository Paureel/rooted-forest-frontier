"""Post-hoc exact checks for the PROOF.md scope audit, not fresh certification.

Expected values were already stated in the proof/author receipt. This script
checks their arithmetic independently and exposes the live-vs-total count issue.
Controls run before using these post-hoc examples.
"""
import json
from pathlib import Path
from partition_oracle import Instance, Tree, restrict
from run_verification import controls, digest

HERE=Path(__file__).resolve().parent
OUTPUT=HERE.parents[1]/'results/triple-dp-verification-proof-scope.json'
assert not OUTPUT.exists()
control_receipt=controls()
original={'target':[['a','b'],['c','d']], 'source':[[['a','c'],['b','d']]]}
child={'target':original['target'], 'source':['a',['c',['b','d']]]}
tidied={'target':['b',['c','d']], 'source':[['c',['b','d']]]}
# Exact expectations retained as post-hoc source claims, not held-out references.
assert Instance(original).exact()['components']==3
assert Instance(child).exact()['components']==3
assert Instance(tidied).exact()['components']==2
r=1
full_m=len(child['source']); full_p=Instance(child).exact()['components']
live_m=len(tidied['source']); live_p=Instance(tidied).exact()['components']
assert r+(full_p-full_m)==2
assert r+(live_p-live_m)==2
assert full_p-1==2
assert live_p-1==1

def cherries(tree):
    reverse={p:x for x,p in tree.leaves.items()}
    return [(reverse[p+(0,)],reverse[p+(1,)]) for p in tree.nodes
            if p+(0,) in reverse and p+(1,) in reverse]

def pendant_count(tree,a,b):
    path=tree.path(a,b)
    return sum(1 for p in path for side in (0,1)
               if p+(side,) in tree.nodes and p+(side,) not in path)
T=Tree(original['target']); S=Tree(original['source'][0])
counts=[]
for direction,left,right in [('T-to-source',T,S),('source-to-T',S,T)]:
    for a,b in cherries(left):
        counts.append({'direction':direction,'cherry':[a,b], 't':pendant_count(right,a,b)})
assert len(counts)==4 and all(row['t']==2 for row in counts)
# Rule4's c is pendant nearest a and forms the source cherry (a,c).
assert ('a','c') in cherries(S)
assert restrict(original['source'][0],frozenset('bcd'))==('c',('b','d'))

# A graph region may enter a child without a terminal there; trimming loses
# that support choice. These are feasible supports with identical leaf blocks.
leaf_regions=[{T.leaves[x]} for x in 'bcd']
minimal_a=set(T.path('a','a')) | {(),(0,)}
padded_a=minimal_a | {(1,)}
def connected(region):
    seen={next(iter(region))}
    while True:
        extra={v for v in region if any(v[:-1]==u or u[:-1]==v for u in seen if v!=u)}
        if extra<=seen: return seen==region
        seen|=extra
for region in (minimal_a,padded_a):
    assert connected(region)
    assert all(not region & other for other in leaf_regions)
    assert [x for x,p in T.leaves.items() if p in region]==['a']
assert minimal_a!=padded_a
receipt={'provenance':'post-hoc proof-scope arithmetic; values already read from author text',
 'controls':control_receipt,'proof_sha256':digest(HERE.parent/'PROOF.md'),
 'script_sha256':digest(Path(__file__)),
 'baseline_example':{'original_components':3,'child_components':3,'tidied_live_components':2,
 'paid_cuts':r,'full_source_components':full_m,'live_source_components':live_m,
 'total_cuts_using_live_increment':2,'full_components_minus_one':2,'live_components_minus_one':1,
 'whidden_path_counts':counts,'source_a_cut_matches_child':True},
 'normal_form_example':{'tree':original['target'], 'minimal_root_open_a':sorted(map(list,minimal_a)),
 'padded_root_open_a':sorted(map(list,padded_a)), 'same_leaf_blocks':[['a'],['b'],['c'],['d']],
 'conclusion':'Trimming leafless boundary branches is many-to-one on unrestricted graph supports.'},
 'theorem_verdict':'OPEN'}
OUTPUT.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print(json.dumps({'output':str(OUTPUT),'original_p':3,'child_p':3,'tidied_live_p':2,
                 'paid_plus_live_increment':2,'live_p_minus_one':1,'all_cherry_path_t':2}))
