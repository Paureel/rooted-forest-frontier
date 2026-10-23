#!/usr/bin/env python3
"""One-shot post-contact reproduction of the author's two literal fixtures.
Uses only the already frozen independent graph instrument. These fixture
values are development contacts, not new preregistration or replication.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4]
spec=importlib.util.spec_from_file_location('frozen_graph_paths',HERE/'graph_paths.py')
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
tripod=[['4','5'],[['0','1'],['2','3']]]
blocks=[['0','2'],['3','4'],['5','1']]
T=g.Original(tripod)
clique=g.helly_observations(T,[T.hull(b) for b in blocks])
assert clique['common_vertices']==['1'] and clique['common_edges']==[]
regions=[g.region_observations(T,b,['1']) for b in blocks]
assert all(r['r']==2 and r['overlap_guard'] for r in regions)
chain=[[['0','1'],'2'],[['3','4'],'5']]
parents=[['1','2'],['0','3'],['4','5']]
c=g.observe({'kind':'chain','tree':chain,'parents':parents,'v':'0','w':'1'})
assert c['overlap_edges']==[[0,1],[1,2]] and c['endpoints_disjoint']
assert c['middle_r']==2 and c['middle_leafless_components']==[['']] and c['middle_coincidence']
root=g.region_observations(g.Original(chain),parents[1],[''])
assert root['r']==2
receipt={'scope':'post-contact author fixture reconstruction with frozen independent BFS graph code; no extra replication',
         'input_origin':'literal Controls.lean definitions; Nat leaf labels bijectively presented as decimal strings',
         'tripod':{'tree':tripod,'parents':blocks,'observed':clique,'parent_regions':regions},
         'chain':{'tree':chain,'parents':parents,'observed':c,'root_regions':root},
         'all_passed':True,'source_hashes':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),HERE/'graph_paths.py',ROOT/'research/rmaf/algorithm/universal233/geometry/Controls.lean']}}
out=ROOT/'research/rmaf/results/algorithm-geometry-fresh-review-author-fixtures.json';assert not out.exists();out.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'author_fixtures_reproduced':2,'tripod_common_vertex':'1','common_edges':0,'chain_joint_leaf_regions':2,'chain_leafless_middle_vertices':['']}))
