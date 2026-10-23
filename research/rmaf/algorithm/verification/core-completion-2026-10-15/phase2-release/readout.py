"""Replay frozen pre-contact fixtures against newly compiled Lean execution."""
import importlib.util, json, sys
from fractions import Fraction
from pathlib import Path
from rebuild import ROOT,HERE,run,digest

FROZEN=HERE.parent/'frozen-v1'
spec=importlib.util.spec_from_file_location('precontact_graph',FROZEN/'independent_instrument.py')
graph=importlib.util.module_from_spec(spec);spec.loader.exec_module(graph)
controls=json.loads((FROZEN/'CONTROLS-v1.json').read_text())

def lit(v):
    if isinstance(v,list): return '['+', '.join(lit(x) for x in v)+']'
    return str(v)
def tree(v):
    if isinstance(v,int):return f'(Tree.leaf {v})'
    return f'(Tree.node {tree(v[0])} {tree(v[1])})'
def color(v):
    return '(fun x => '+''.join(f'if x = {k} then {c} else ' for k,c in v.items())+'0)'
def line(tag,expr):return '#eval IO.println ("'+tag+'|" ++ ('+expr+').compress)\n'

def main():
    build=HERE/'isolated-source'
    out='''import RationalMass
import Lean
open RMAF Universal233.CoreProgram Universal233.SourceCoverage Lean
def outputJSON (o : Output) : Json := Json.mkObj [
  ("partition",toJson o.partition),
  ("cuts",toJson (o.sourceCuts.map (fun p => p.map (fun b => if b then 1 else 0))))]
def receiptJSON (r : Receipt) : Json := Json.mkObj [
  ("outputs",toJson (r.outputs.map outputJSON)),("refusals",toJson r.refusals),
  ("visited",toJson r.visited),("attempts",toJson r.childAttempts),("pruned",toJson r.pruned)]
def qJSON (q : Rat) : Json := Json.mkObj [("num",toJson q.num),("den",toJson q.den)]
def refinesB (xs ys : List (List Nat)) : Bool :=
  xs.all (fun b => ys.any (fun a => b.all (fun x => a.contains x)))
'''
    for f in controls['program']:
        out+=line('PROGRAM:'+f['id'],f'receiptJSON (generate {tree(f["tree"])} {color(f["colors"])} {f["q"]})')
    for f in controls['partitions']:
        t,bs,qs,col=tree(f['tree']),lit(f['F']),lit(f['Q']),color(f['colors'])
        fields=[('proper',f'partitionCheck (leaves {t}) {bs}'),
          ('convex',f'pairwiseEmbeddings {t} {bs}'),
          ('monochromatic',f'({bs} : List (List Nat)).all (fun b => b.all (fun x => b.all (fun y => {col} x == {col} y)))'),
          ('F_refines_Q',f'refinesB {bs} {qs}'),('Q_refines_F',f'refinesB {qs} {bs}')]
        expr='Json.mkObj ['+', '.join(f'("{k}",toJson ({v}))' for k,v in fields)+']'
        out+=line('PARTITION:'+f['id'],expr)
    for i,f in enumerate(controls['proper_labels']):
        out+=line('PROPER:'+str(i),f'toJson (decide (({lit(f["labels"])} : List Nat).Perm (List.range {f["n"]})))')
    out+='def fixtureOutputs := (generate Controls.crossed Controls.parity 2).outputs\n'
    for f in controls['mass']:
        os='['+', '.join(f'(fixtureOutputs.getD {i} ⟨[],[]⟩)' for i in f['output_refs'])+']'
        out+=line('MASS:'+f['id'],f'Json.mkObj [("cost_sum",toJson (({os}).map (fun o => o.sourceCuts.length)).sum),("mass_at_2",qJSON (rawQMass 2 {os})),("mass_at_233_100",qJSON (rawQMass (233/100) {os}))]')
    (build/'FreshReadout.lean').write_text(out)
    b=run(build,'FreshReadout'); assert b['exit']==0,b
    actual={}
    for s in (build/'FreshReadout.log').read_text().splitlines():
        if '|' in s and s.split('|',1)[0].startswith(('PROGRAM:','PARTITION:','MASS:','PROPER:')):
            key,value=s.split('|',1);actual[key]=json.loads(value)
    results=[]; negative=[]
    for f in controls['program']:
        a=actual['PROGRAM:'+f['id']]
        expected={'outputs':[{'partition':p,'cuts':c} for p,c in zip(f['parts'],f['cuts'])],
          'refusals':[f['refusal']] if 'refusal' in f else [],
          **{k:f[k] for k in ('visited','attempts','pruned')}}
        assert a==expected,(f['id'],a,expected)
        own=graph.generate(f['tree'],{int(k):v for k,v in f['colors'].items()},f['q'])
        assert all(own[k]==a[k] for k in a)
        emitted=[]
        for o in a['outputs']:
            witness=graph.OriginalGraph(f['tree']).residual(o['cuts'])
            assert witness['nonempty'] and witness['cuts_plus_one']
            assert witness['leaf_partition']==graph.canonical(o['partition'])
            assert graph.proper_partition(graph.OriginalGraph(f['tree']),o['partition'])
            assert graph.monochromatic(o['partition'],{int(k):v for k,v in f['colors'].items()})
            costs=len(o['cuts']);assert len(set(f['colors'].values()))-1<=costs<=min(f['q'],len(graph.syntax_leaves(f['tree']))-1)
            emitted.append(witness)
        results.append({'id':f['id'],'actual':a,'exact_frozen_match':True,'independent_match':True,'original_graph_witnesses':emitted})
    for f in controls['partitions']:
        a=actual['PARTITION:'+f['id']]
        assert all(v==f[k] for k,v in a.items()),(f['id'],a)
    for i,f in enumerate(controls['proper_labels']):assert actual['PROPER:'+str(i)]==f['expected']
    for f in controls['mass']:
        a=actual['MASS:'+f['id']];assert a['cost_sum']==f['cost_sum']
        for k in ('mass_at_2','mass_at_233_100'):
            assert Fraction(a[k]['num'],a[k]['den'])==Fraction(*f[k])
    duplicate=actual['MASS:duplicate-emission-list'];dedup=actual['MASS:actual-crossed-list']
    for k in duplicate:negative.append({'false_claim':'omit duplicate '+k,'caught':duplicate[k]!=dedup[k]})
    costs=[len(o['cuts']) for o in actual['PROGRAM:crossed-q2']['outputs']]
    negative.append({'false_claim':'all emitted costs >=3','caught':not all(c>=3 for c in costs)})
    negative.append({'false_claim':'crossed q1 emits','caught':not actual['PROGRAM:crossed-q1']['outputs']})
    strict=actual['PARTITION:strict-forward-refinement']
    negative.extend([{'false_claim':'reverse refinement','caught':not strict['Q_refines_F']},
                     {'false_claim':'equal partitions','caught':controls['partitions'][0]['F']!=controls['partitions'][0]['Q']}])
    assert all(r['caught'] for r in negative)
    report={'status':'PASS_SCOPED_EXECUTABLE_REPLAY','build':b,'readout_sha256':digest(build/'FreshReadout.lean'),
      'precontact_controls_sha256':digest(FROZEN/'CONTROLS-v1.json'),
      'precontact_instrument_sha256':digest(FROZEN/'independent_instrument.py'),
      'program_fixture_count':len(results),'program_results':results,'all_actual_readouts':actual,
      'false_expectation_controls':negative,'replication_count_added':0,
      'universal_proof_acceptance_inferred_from_fixtures':False}
    path=ROOT/'research/rmaf/results/algorithm-core-completion-fresh-review-actual-readout-v1.json'
    path.write_text(json.dumps(report,indent=2)+'\n')
    print(report['status'],len(results),'program fixtures;',len(negative),'explicit false comparisons caught')

if __name__=='__main__':main()
