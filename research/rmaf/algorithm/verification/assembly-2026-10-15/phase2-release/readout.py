"""Actual compiled execution versus unchanged prerelease literal expectations."""
from pathlib import Path
import sys,importlib.util,json,collections
from fractions import Fraction
from rebuild import ROOT,HERE,run,digest
sys.dont_write_bytecode=True
PRE=HERE.parent
spec=importlib.util.spec_from_file_location('own_prerelease',PRE/'instrument.py')
I=importlib.util.module_from_spec(spec);spec.loader.exec_module(I)
C=json.loads((PRE/'CONTROLS-v1.json').read_text())
A=json.loads((PRE/'CONTROL-ADDENDUM-v1.json').read_text())

def lit(v):
    if isinstance(v,list):return '['+', '.join(lit(x) for x in v)+']'
    return str(v)
def tree(t):
    return f'(Tree.leaf {t})' if type(t) is int else f'(Tree.node {tree(t[0])} {tree(t[1])})'
def vertex(v):return '['+', '.join('true' if b else 'false' for b in v)+']'
def req(mode,M):
    if mode=='constant':return 'Assembly.Request.keep'
    if mode=='joint':return f'(Assembly.Request.both {vertex(M["v"])} {vertex(M["w"])})'
    return f'(Assembly.Request.at {vertex(M[mode])})'
def emit(k,e):return '#eval IO.println ("'+k+'|" ++ ('+e+').compress)\n'
def hist(o):return json.dumps(o,sort_keys=True,separators=(',',':'))

def main():
    b=HERE/'isolated-completion'
    text='''import HardPaid
import Lean
open RMAF Universal233 CoreProgram SourceCoverage VertexGeometry Lean
def outputJSON (o : Output) : Json := Json.mkObj [
 ("partition",toJson o.partition),("cuts",toJson (o.sourceCuts.map (fun p => p.map (fun b => if b then 1 else 0))))]
def outputsJSON (os : List Output) : Json := toJson (os.map outputJSON)
def ratJSON (q : Rat) : Json := Json.mkObj [("num",toJson q.num),("den",toJson q.den)]
def colorJSON (S : Tree) (c : Nat → Nat) : Json := Json.mkObj ((leaves S).map (fun x => (toString x,toJson (c x))))
def refineBool (F Q : List (List Nat)) : Bool := F.all (fun b => Q.any (fun a => b.all a.contains))
def clearBool (T : Tree) (F : List (List Nat)) (v : RMAF.Vertex) : Bool := F.all (fun p => !(minimalVertices p T).contains v)
'''
    author_orders={
      'clique':['leave-A','leave-B','leave-C'],
      'four-chain':['B-v-C-w','B-joint','A-v-C-w','A-v-B-w'],
      'two-joint-diagonal':['B-joint','A-v-C-w']}
    for j,M in enumerate(C['macros']):
        T,S,P=tree(M['target']),tree(M['source']),M['parents'];pa,pb=lit(P[0]),lit(P[1])
        text+=f'def source{j} : Tree := {S}\ndef target{j} : Tree := {T}\n'
        for k,call in enumerate(M['calls']):
            args=' '.join(req(x,M) for x in call['modes']);fn=f'color{j}_{k}'
            text+=f'def {fn} : Nat → Nat := Assembly.requestedColor target{j} {pa} {pb} {args}\n'
            out=f'(generate source{j} {fn} {M["q"]}).outputs'
            key=M['id']+':'+call['id']
            text+=emit('COLOR:'+key,f'colorJSON source{j} {fn}')
            text+=emit('CALL:'+key,'outputsJSON '+out)
            text+=emit('COUNT:'+key,f'toJson [(dedupNat (({lit(P[0])} : List Nat).map {fn})).length,(dedupNat (({lit(P[1])} : List Nat).map {fn})).length,(dedupNat (({lit(P[2])} : List Nat).map {fn})).length,(dedupNat ((leaves source{j}).map {fn})).length]')
            if M['id']=='two-joint-diagonal':text+=emit('Q3:'+key,f'outputsJSON (generate source{j} {fn} 3).outputs')
        function={'clique':'cliqueOutputs','four-chain':'fourChainOutputs','two-joint-diagonal':'diagonalOutputs'}[M['id']]
        positions=vertex(M['v'])+(' '+vertex(M['w']) if 'w' in M else '')
        whole=f'(WholeSourceMass.{function} source{j} target{j} {pa} {pb} {positions} {M["q"]})'
        text+=emit('MACRO:'+M['id'],'outputsJSON '+whole)
        text+=emit('MASS2:'+M['id'],'ratJSON (rawQMass 2 '+whole+')')
        text+=emit('MASS233:'+M['id'],'ratJSON (rawQMass (233/100) '+whole+')')
        for target in ['v','w']:
            if target in M:text+=emit('REGION:'+M['id']+':'+target,f'toJson [{", ".join(f"(regions {lit(p)} target{j} {vertex(M[target])}).length" for p in P)}]')
        if 'w' in M:text+=emit('JOINT:'+M['id'],f'toJson ((jointColors {pb} target{j} {vertex(M["v"])} {vertex(M["w"])}).map (fun p => [p.1,p.2]))')
    H=C['hard_parent'];T,S=tree(H['target']),tree(H['source'])
    for k,t in [('original',H['source']),('mirror',H['mirror_source']),('inner_swap',H['inner_swap_source'])]:
        source=tree(t)
        edges=H['pendant_cuts'] if k=='original' else H[k+'_cuts']
        text+=emit('HARD-CUTS:'+k,f'toJson ((HardParent.pendantOriginal {source} 0 1).map (fun p => p.map (fun b => if b then 1 else 0)))')
        text+=emit('HARD-PARENTS:'+k,f'toJson (HardParent.literalThree {source} {vertex(edges[0])} {vertex(edges[1])})')
        forest_checks=', '.join('agreement '+T+' '+source+' '+lit(x['F']) for x in H['agreement_partitions'])
        text+=emit('HARD-AGREEMENT:'+k,'toJson ['+forest_checks+']')
    for k,f in enumerate(H['agreement_partitions']):
        text+=emit('HARD-REFINE:'+str(k),f'toJson (refineBool {lit(f["F"])} {lit(H["parents"])})')
    E=C['clearing_not_final_agreement'];args=' '.join(req(m,E) for m in E['modes'])
    text+=f'def badSource : Tree := {tree(E["source"])}\ndef badTarget : Tree := {tree(E["target"])}\n'
    bad=f'(generate badSource (Assembly.requestedColor badTarget {lit(E["parents"][0])} {lit(E["parents"][1])} {args}) {E["q"]}).outputs'
    text+=emit('CLEAR-NOT-AGREE:outputs','outputsJSON '+bad)
    text+=emit('CLEAR-NOT-AGREE:agreement',f'toJson (({bad}).map (fun o => agreement badTarget badSource o.partition))')
    for f in C['geometry_exceptions']:
        if 'parent' in f:
            text+=emit('EXCEPTION:'+f['id'],f'Json.mkObj [("colors",toJson (({lit(f["parent"])} : List Nat).map (colorLabel {tree(f["tree"])} {vertex(f["v"])}))),("clears",toJson (clearBool {tree(f["tree"])} [{lit(f["parent"])}] {vertex(f["v"])}))]')
        else:text+=emit('EXCEPTION:'+f['id'],f'toJson (HardParent.pendantOriginal {tree(f["tree"])} {f["a"]} {f["b"]}).length')
    for f in C['malformed_parents']+[{'id':'proper-but-crossing','tree':A['proper_but_crossing_source_parents']['source'],'parents':A['proper_but_crossing_source_parents']['parents']}]:
        text+=emit('PARENTS:'+f['id'],f'toJson [partitionCheck (leaves {tree(f["tree"])}) {lit(f["parents"])},pairwiseEmbeddings {tree(f["tree"])} {lit(f["parents"])}]')
    (b/'FreshReadout.lean').write_text(text)
    r=run(b,'FreshReadout');assert not r['exit'],r
    actual={}
    for s in (b/'FreshReadout.log').read_text().splitlines():
        if '|' in s:
            key,value=s.split('|',1)
            if key.startswith(('COLOR:','CALL:','COUNT:','Q3:','MACRO:','MASS2:','MASS233:','REGION:','JOINT:','HARD-','CLEAR-NOT-AGREE:','EXCEPTION:','PARENTS:')):actual[key]=json.loads(value)
    checks=[];order_records=[]
    def check(name,v,e):
        assert v==e,(name,v,e)
        checks.append({'id':name,'pass':True})
    for M in C['macros']:
        bycall={}
        for call in M['calls']:
            key=M['id']+':'+call['id'];out=actual['CALL:'+key]
            expected=[{'partition':p,'cuts':c} for p,c in zip(call['parts'],call['cuts'],strict=True)]
            check(key+' literal output',out,expected)
            check(key+' literal color',actual['COLOR:'+key],call['colors'])
            check(key+' actual color counts',actual['COUNT:'+key],call['local_counts']+[call['global_count']])
            colors={int(k):v for k,v in call['colors'].items()}
            for o in out:
                check(key+' original output',I.validate_output(M['source'],colors,M['q'],o),True)
                check(key+' source embedding',I.base.convex_partition(I.base.OriginalGraph(M['source']),o['partition']),True)
                check(key+' parent containment',I.base.refines(o['partition'],M['parents']),True)
                check(key+' requested clears',I.requested_clear(M['target'],M['parents'],o['partition'],call['requests'],M),True)
            bycall[call['id']]=out
        reference=[o for c in M['calls'] for o in bycall[c['id']]]
        ordered=[o for name in author_orders[M['id']] for o in bycall[name]]
        actual_whole=actual['MACRO:'+M['id']]
        check(M['id']+' actual literal macro concatenation',actual_whole,ordered)
        check(M['id']+' reference multiplicity-preserving permutation',collections.Counter(map(hist,actual_whole)),collections.Counter(map(hist,reference)))
        order_records.append({'id':M['id'],'frozen_reference_order':[c['id'] for c in M['calls']],
          'actual_author_order':author_orders[M['id']],'order_equal':reference==actual_whole,
          'same_output_multiset_with_multiplicity':True,'reference_expectations_changed':False})
        for prefix,key in [('MASS2:','mass_at_2'),('MASS233:','mass_at_233_100')]:
            q=actual[prefix+M['id']];check(M['id']+' '+key,Fraction(q['num'],q['den']),Fraction(*M[key]))
        for pos in ['v','w']:
            if pos in M:check(M['id']+' region '+pos,actual['REGION:'+M['id']+':'+pos],M['parent_region_counts_at_'+pos])
        if 'w' in M:check(M['id']+' joint pairs',actual['JOINT:'+M['id']],M['B_joint_pairs'])
        for f in M['forests']:
            covering=[]
            for call in M['calls']:
                key=M['id']+':'+call['id'];os=actual['Q3:'+key] if f.get('q')==3 else bycall[call['id']]
                if any(I.base.refines(f['F'],o['partition']) for o in os):covering.append(call['id'])
            check(M['id']+f['id']+' only covering call',covering,[f['only_covering_call']])
        if M['id']=='two-joint-diagonal':check('diagonal q3', [len(actual['Q3:'+M['id']+':'+call['id']]) for call in M['calls']],M['q3_output_counts'])
    for label in ['original','mirror','inner_swap']:
        check('hard cuts '+label,actual['HARD-CUTS:'+label],H['pendant_cuts'] if label=='original' else H[label+'_cuts'])
        check('hard parents '+label,I.base.canonical(actual['HARD-PARENTS:'+label]),H['parents'])
        check('hard all15 agreement '+label,actual['HARD-AGREEMENT:'+label],[x['agreement'] for x in H['agreement_partitions']])
    for k,f in enumerate(H['agreement_partitions']):
        if f['agreement']:check('hard refinement '+str(k),actual['HARD-REFINE:'+str(k)],f['refines_P'])
    check('clearing not agreement literal',actual['CLEAR-NOT-AGREE:outputs'],[{'partition':p,'cuts':c} for p,c in zip(E['parts'],E['cuts'],strict=True)])
    check('clearing not agreement actual Boolean',actual['CLEAR-NOT-AGREE:agreement'],[False])
    for f in C['geometry_exceptions']:
        got=actual['EXCEPTION:'+f['id']]
        if 'parent' in f:
            check(f['id']+' region colors',sorted(set(got['colors'])),f['regions'])
            if 'clears' in f:check(f['id']+' actual clearing',got['clears'],f['clears'])
        else:check(f['id']+' actual pendant count',got,f['pendant_count'])
    for f in C['malformed_parents']:check('bad parent '+f['id'],all(actual['PARENTS:'+f['id']]),False)
    check('proper but crossing source',actual['PARENTS:proper-but-crossing'],[True,False])
    report={'status':'PASS_FROZEN_LITERAL_ACTUAL_READOUT','readout_build':r,
      'readout_source_sha256':digest(b/'FreshReadout.lean'),'frozen_controls_sha256':digest(PRE/'CONTROLS-v1.json'),
      'frozen_instrument_sha256':digest(PRE/'instrument.py'),'checks':checks,'check_count':len(checks),
      'actual':actual,'order_adapters':order_records,'numeric_joint_encoding':'same base4 encoding; no numeric adapter required',
      'hard_parent_order':'author names [pendant p,pendant r,root] versus frozen canonical component display [root,p,r]; same exact component partition, graph/membership expectations unchanged',
      'replication_count_added':0,'all_main_milestones':'OPEN'}
    (ROOT/'research/rmaf/results/algorithm-assembly-fresh-review-actual-readout-v1.json').write_text(json.dumps(report,indent=2)+'\n')
    print(report['status'],len(checks),'exact comparisons; four-chain order permutation explicitly recorded')

if __name__=='__main__':main()
