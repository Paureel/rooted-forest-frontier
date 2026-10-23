"""Literal graph interpretation checks; bounded to the frozen small fixtures."""
import json
from readout import graph,controls,tree,lit,color
from rebuild import ROOT,HERE,run,digest

def vertex(xs):return '['+', '.join('true' if x else 'false' for x in xs)+']'
def cuts(xs):return '['+', '.join(vertex(x) for x in xs)+']'

def main():
    b=HERE/'joint-copy'
    text='''import NonauthorConsumer
open RMAF Universal233.CoreGraph Universal233.CoreProgram Universal233.CutRealization
'''
    rows=[];assertions=0
    for f in controls['graph']:
        g=graph.OriginalGraph(f['tree']);w=g.residual(f['cuts']);t=tree(f['tree'])
        assert w['leaf_partition']==f['components'] and w['nonempty']==f['nonempty'] and w['count']==f['component_count']
        removed={frozenset(g.edge(a)) for a in f['cuts']}
        # Both edge orientations for every actual original edge. This is not
        # a tree census: the fixed six tiny literal fixture graphs are the input.
        for v,where in g.address.items():
            text+=f'example : Valid {t} {vertex(where)} := ⟨_,rfl⟩\n';assertions+=1
            if v in g.leaf:text+=f'example : LeafAt {t} {vertex(where)} {g.leaf[v]} := rfl\n';assertions+=1
            for u in sorted(g.adj[v]):
                adj=f'Adj {t} {vertex(where)} {vertex(g.address[u])}'
                radj=f'ResidualAdj {t} {cuts(f["cuts"])} {vertex(where)} {vertex(g.address[u])}'
                survives=frozenset((v,u)) not in removed
                text+=f'example : {adj} := by simp [Adj,Valid,subtree]\n'
                text+=f'example : '+('' if survives else '¬ ')+radj+' := by simp [ResidualAdj,Adj,Valid,subtree]\n'
                assertions+=2
        rows.append({'id':f['id'],'original_graph':w,'literal_frozen_match':True})
    t=tree([[0,1],2])
    text+=f'''example : ¬ Adj {t} [] [false,true] := by simp [Adj,Valid,subtree]
example : ResidualWalk {t} [[false,false]] [] [false,true] := by
  apply ResidualWalk.step (v := [false])
  · simp [ResidualAdj,Adj,Valid,subtree]
  apply ResidualWalk.step (v := [false,true])
  · simp [ResidualAdj,Adj,Valid,subtree]
  exact ResidualWalk.refl ⟨_,rfl⟩
example : ¬ RealizedOutput (.node (.leaf 0) (.leaf 1))
    ⟨[[0],[1]],[[false],[true]]⟩ := by
  intro h
  obtain ⟨_,_,components,_,_,_,_,_,_,_,hcost⟩ := h
  simp at hcost
''';assertions+=3
    for f in controls['invalid_cuts']:
        try:graph.OriginalGraph(f['tree']).residual(f['cuts']);assert False
        except ValueError:pass
    add=json.loads((HERE.parent/'frozen-v2/CONTROL-ADDENDUM-v1.json').read_text())
    addrows=[]
    for f in add['cases']:
        o=f['output'];t=tree(f['tree']);col=color(f['colors'])
        output='(⟨'+lit(o['partition'])+', '+cuts(o['cuts'])+'⟩ : Output)'
        pred=f'{output} ∈ (generate {t} {col} {f["q"]}).outputs'
        text+='example : '+('' if f['expected_valid'] else '¬ ')+pred+' := by decide +kernel\n';assertions+=1
        valid=graph.validate_emission(f['tree'],{int(k):v for k,v in f['colors'].items()},f['q'],o)
        assert valid==f['expected_valid']
        addrows.append({'id':f['id'],'actual_valid':valid,'flipped_expectation_caught':valid!=not_(f['expected_valid'])})
    (b/'FreshGraphControls.lean').write_text(text)
    build=run(b,'FreshGraphControls');assert build['exit']==0,build
    # Replay own suppression model and preserve the FULL original path. The
    # Lean controls above independently use exactly those two original edges.
    g=graph.OriginalGraph([[0,1],2]);path=[list(g.address[v]) for v in g.path(g.at[()],g.at[(0,1)])]
    assert path==[[],[0],[0,1]]
    report={'status':'PASS_LITERAL_ORIGINAL_GRAPH_CONTROLS','pilot_seconds':0.34415154199996323,
      'build':build,'assertions':assertions,'source_sha256':digest(b/'FreshGraphControls.lean'),
      'graph_fixtures':rows,'invalid_original_cut_controls':3,'suppression_original_path':path,
      'forged_compressed_edge_rejected_in_Lean':True,'leafless_cut_realization_rejected_in_Lean':True,
      'addendum_actual_membership_controls':addrows,'replication_count_added':0}
    (ROOT/'research/rmaf/results/algorithm-core-completion-fresh-review-graph-controls-v1.json').write_text(json.dumps(report,indent=2)+'\n')
    print(report['status'],assertions,'literal assertions; six graphs/four addendum cases')

def not_(x):return not x
if __name__=='__main__':main()
