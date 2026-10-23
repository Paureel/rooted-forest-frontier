#!/usr/bin/env python3
"""One-shot independent adapter of pre-candidate literals to Lean controls.
No proof or value is imported from the author's controls/audit orchestration.
"""
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
BUILD = HERE/'lean-isolated'
pin = json.loads((HERE/'CONTROL-PIN.json').read_text())
frozen = json.loads((HERE/'PRE-CANDIDATE-FREEZE.json').read_text())
for p,h in frozen['files_sha256'].items():
    assert hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h
spec = importlib.util.spec_from_file_location('frozen_graph_paths',HERE/'graph_paths.py')
graph = importlib.util.module_from_spec(spec)
spec.loader.exec_module(graph)
previous = json.loads((ROOT/'research/rmaf/results/algorithm-geometry-fresh-review-controls-v1.json').read_text())
assert previous['result']['all_passed']
observed = {r['id']:r['observed'] for r in previous['result']['rows']}
alphabet = ['a','b','c','d','e','f','m','u','x','y','z']
labels = {x:i for i,x in enumerate(alphabet)}
def tree(t):
    return f'(.leaf {labels[t]})' if isinstance(t,str) else f'(.node {tree(t[0])} {tree(t[1])})'
def vertex(v):
    return '['+','.join('false' if b=='0' else 'true' for b in v)+']'
def verts(vs):
    return '['+','.join(vertex(v) for v in vs)+']'
def block(b):
    return '['+','.join(str(labels[x]) for x in b)+']'
def blocks(bs):
    return '['+','.join(block(b) for b in bs)+']'
def boolean(b):
    return 'true' if b else 'false'
declarations = []
mapping = []
def add(case, tag, proposition):
    name = f'control_{len(declarations)+1:03d}'
    declarations.append(f'theorem {name} : {proposition} := by decide +kernel\n')
    mapping.append({'theorem':'GeometryFreshControls.'+name,'case':case,'meaning':tag,
                    'proposition':proposition,'expected_from':'pre-candidate CONTROL-PIN.json / frozen independent observations'})

header = '''import Composition
namespace GeometryFreshControls
open RMAF VertexGeometry
def sameVertices (a b : List VertexGeometry.Vertex) : Bool :=
  a.all b.contains && b.all a.contains
def forestCheck (t : Tree) (ss : List Tree) (F : List (List Nat)) : Bool :=
  partitionCheck (leaves t) (ss.map leaves) && partitionCheck (leaves t) F &&
  pairwiseEmbeddings t F &&
  F.all (fun P =>
    let owners := ss.filter (fun s => P.all (leaves s).contains)
    owners.length == 1 && match owners.head? with
      | none => false
      | some s => restrictionAgrees t s P) &&
  ss.all (fun s => pairwiseEmbeddings s (F.filter (fun P => P.all (leaves s).contains)))
'''
for case in pin['cases']:
    kind,id = case['kind'],case['id']
    obs = observed[id]
    if kind=='hull' and case['tree'] is not None:
        expression=f'minimalVertices {block(case["block"])} {tree(case["tree"])}'
        add(id,'actual original minimal vertices',f'sameVertices ({expression}) {verts(case["expected"]["hull"])} = true')
    if kind=='helly':
        t=tree(case['tree']); hs=[f'(minimalVertices {block(b)} {t})' for b in case['blocks']]
        target=case['expected']['selector']; expected='none' if target is None else 'some '+vertex(target)
        add(id,'actual selector',f'findCommon {" ".join(hs)} = {expected}')
    if kind=='regions':
        t=tree(case['tree']);D=block(case['parent']);removed=case['removed']
        if len(removed)==1:
            add(id,'nonempty leaf region count',f'(regions {D} {t} {vertex(removed[0])}).length = {case["expected"]["r"]}')
        else:
            add(id,'nonempty joint leaf region count',f'(jointColors {D} {t} {vertex(removed[0])} {vertex(removed[1])}).length = {case["expected"]["r"]}')
        if 'avoiding_subsets' in case['expected']:
            allowed={tuple(b) for b in case['expected']['avoiding_subsets']}
            for p in graph.nonempty_subsets(case['parent']):
                expr=f'{verts(removed)}.all (fun v => !(minimalVertices {block(p)} {t}).contains v)'
                add(id,'avoiding original piece '+','.join(p),f'({expr}) = {boolean(tuple(p) in allowed)}')
        if obs['covers_parent_labels']:
            for a,b in itertools.combinations_with_replacement(sorted(case['parent']),2):
                same=any(a in r and b in r for r in case['expected']['leaf_regions'])
                left=[f'colorLabel {t} {vertex(v)} {labels[a]}' for v in removed]
                right=[f'colorLabel {t} {vertex(v)} {labels[b]}' for v in removed]
                expr=(f'({left[0]}) == ({right[0]})' if len(removed)==1 else
                      f'({left[0]}, {left[1]}) == ({right[0]}, {right[1]})')
                add(id,'original-label region relation '+a+','+b,f'({expr}) = {boolean(same)}')
    if kind=='chain':
        t=tree(case['tree']);D=block(case['parents'][1]);v,w=vertex(case['v']),vertex(case['w'])
        add(id,'actual middle joint leaf region count',f'(jointColors {D} {t} {v} {w}).length = {case["expected"]["middle_r"]}')
        if case['expected']['middle_coincidence']:
            for p in graph.nonempty_subsets(case['parents'][1]):
                add(id,'coincident occupancy '+','.join(p),f'(minimalVertices {block(p)} {t}).contains {v} = (minimalVertices {block(p)} {t}).contains {w}')
        else:
            p=block(case['piece']);occ=case['expected']['piece_occupancy']
            add(id,'noncoincidence witness',f'(minimalVertices {p} {t}).contains {v} = {boolean(occ[0])} ∧ (minimalVertices {p} {t}).contains {w} = {boolean(occ[1])}')
    if kind=='state' and case['target'] is not None:
        ss='['+','.join(tree(s) for s in case['sources'])+']'
        add(id,'finite original-label forest check',f'forestCheck {tree(case["target"])} {ss} {blocks(case["partition"])} = {boolean(case["expected"]["valid"])}')

body=header+'\n'.join(declarations)+'\nend GeometryFreshControls\n'
path=BUILD/'GeometryFreshControls.lean';assert not path.exists();path.write_text(body)
false = '''import GeometryFreshControls
namespace GeometryFreshNegative
open RMAF VertexGeometry
-- Pre-candidate below-root false expectation: the original root is absent.
theorem false_original_root :
  ([] : VertexGeometry.Vertex) ∈ minimalVertices [1,2] (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) := by decide +kernel
-- Pre-candidate leafless middle false expectation: it contributes no third color.
theorem false_leafless_third_color :
'''
chain=next(c for c in pin['cases'] if c['id']=='actual-chain-two-regions')
false+=f'  (jointColors {block(chain["parents"][1])} {tree(chain["tree"])} {vertex(chain["v"])} {vertex(chain["w"])}).length = 3 := by decide +kernel\nend GeometryFreshNegative\n'
path=BUILD/'GeometryFreshNegative.lean';assert not path.exists();path.write_text(false)
out=HERE/'LEAN-CONTROL-MAP.json';assert not out.exists();out.write_text(json.dumps({'scope':'kernel finite comparisons generated from frozen independent literal controls; no new replication','label_map':labels,'declarations':mapping,'excluded_candidate_domains':['empty tree null plumbing has no RMAF.Tree constructor','malformed input rejection is external to RMAF.Tree syntax','actual source cuts/history have no realized implementation in geometry release'],'generated_sources_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [BUILD/'GeometryFreshControls.lean',BUILD/'GeometryFreshNegative.lean']}},indent=2)+'\n')
print(json.dumps({'finite_control_declarations':len(declarations),'false_proof_plants':2}))
