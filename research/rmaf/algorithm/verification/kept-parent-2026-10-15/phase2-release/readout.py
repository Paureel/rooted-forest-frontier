"""Actual compiled raw lists and original model checks versus frozen controls."""
from pathlib import Path
import importlib.util,json,sys
sys.dont_write_bytecode=True
import rebuild as R
PRE=R.HERE.parent
spec=importlib.util.spec_from_file_location('own_kept_preparation',PRE/'instrument.py');I=importlib.util.module_from_spec(spec);spec.loader.exec_module(I)
E=json.loads((PRE/'EXPECTATIONS-v2.json').read_text())
def lit(x):
    if isinstance(x,list):return '['+', '.join(lit(t) for t in x)+']'
    return str(x)
def tree(t):return f'(Tree.leaf {t})' if type(t) is int else f'(Tree.node {tree(t[0])} {tree(t[1])})'
def emit(key,expr):return '#eval IO.println ("'+key+'|" ++ ('+expr+').compress)\n'
def configkey(t,c,q):return json.dumps([t,sorted(c.items()),q],separators=(',',':'))
def original_guards(t,P):
    g=I.graph.OriginalGraph(t);flat=[x for b in P for x in b]
    part=all(P) and all(flat.count(x)==1 for x in g.labels) and all(x in g.labels for x in flat)
    spans=[]
    for b in P:
        vs=[v for v,x in g.leaf.items() if x in b]
        spans.append(set(vs).union(*(set(g.path(vs[0],v)) for v in vs[1:])) if vs else set())
    emb=all(not spans[i]&spans[j] for i in range(len(spans)) for j in range(i))
    return [part,emb,len(set(g.labels))==len(g.labels),len(P)==3]

def main():
    text='''import KeptConsumers
import Lean
open RMAF Universal233 CoreProgram KeptParent Lean
def outputJSON (o : Output) : Json := Json.mkObj [("partition",toJson o.partition),
 ("cuts",toJson (o.sourceCuts.map (fun p => p.map (fun b => if b then 1 else 0))))]
def receiptJSON (r : Receipt) : Json := Json.mkObj [
 ("outputs",toJson (r.outputs.map outputJSON)),("refusals",toJson r.refusals),
 ("visited",toJson r.visited),("attempts",toJson r.childAttempts),("pruned",toJson r.pruned)]
def treeJSON : Tree → Json
 | .leaf x => toJson x
 | .node a b => Json.arr #[treeJSON a,treeJSON b]
def restrictionJSON (S : Tree) (A : List Nat) : Json :=
 match restrict A S with | none => Json.null | some s => treeJSON s
def guards (S : Tree) (P : List (List Nat)) : Json := toJson [
 partitionCheck (leaves S) P,pairwiseEmbeddings S P,decide (leaves S).Nodup,P.length == 3]
'''
    for j,f in enumerate(E['fixtures']):
        P=f['parents'];beta='(fun x => '+''.join(f'if x = {k} then {v} else ' for k,v in f['beta'].items())+'0)'
        text+=f'def S{j} : Tree := {tree(f["tree"])}\ndef color{j} := keepColor {lit(P[0])} {lit(P[1])} {beta}\n'
        text+=emit('GUARDS:'+f['id'],f'guards S{j} {lit(P)}')
        text+=emit('RESTRICT-A:'+f['id'],f'restrictionJSON S{j} {lit(P[0])}')
        text+=emit('RESTRICT-C:'+f['id'],f'restrictionJSON S{j} {lit(P[2])}')
        text+=emit('COLORS:'+f['id'],f'toJson ((leaves S{j}).map (fun x => (x,color{j} x)))')
        for b in f['budgets']:text+=emit(f'GENERATE:{f["id"]}:{b["q"]}',f'receiptJSON (generate S{j} color{j} {b["q"]})')
    for f in E['malformed_sources']:
        text+=emit('MALFORMED:'+f['id'],f'guards {tree(f["tree"])} {lit(f["parents"])}')
        if 'generator_refusal' in f:text+=emit('DUPLICATE-REFUSAL',f'receiptJSON (generate {tree(f["tree"])} (fun _ => 0) 9)')
    source=R.BUILD/'FreshReadout.lean';source.write_text(text)
    H=R.helper();build=H.run(R.BUILD,'FreshReadout',['-o','FreshReadout.olean']);assert build['exit']==0,build
    actual={}
    for line in (R.BUILD/'FreshReadout.log').read_text().splitlines():
        if '|' in line:
            k,v=line.split('|',1)
            if k.startswith(('GUARDS:','RESTRICT-','COLORS:','GENERATE:','MALFORMED:','DUPLICATE-')):
                assert k not in actual,('duplicate-readout',k);actual[k]=json.loads(v)
    checks=[];cache={};owntraces=[]
    def check(name,v,e):
        checks.append({'id':name,'pass':v==e});assert v==e,(name,v,e)
    for f in E['fixtures']:
        name=f['id'];t=f['tree'];P=f['parents'];colors=I.source_colors(t,P,f['beta'])
        check(name+'/actual-original-guards',actual['GUARDS:'+name],original_guards(t,P))
        check(name+'/actual-proper-source',all(actual['GUARDS:'+name]),f['proper_source'])
        check(name+'/actual-restriction-A',actual['RESTRICT-A:'+name],f['restriction_A'])
        check(name+'/actual-restriction-C',actual['RESTRICT-C:'+name],f['restriction_C'])
        check(name+'/actual-arbitrary-B-color',actual['COLORS:'+name],[[x,colors[x]] for x in I.graph.syntax_leaves(t)])
        for b in f['budgets']:
            r=actual[f'GENERATE:{name}:{b["q"]}'];k=configkey(t,colors,b['q'])
            check(name+f'/q{b["q"]}/frozen-literal-list',r['outputs'],b['outputs'])
            reference=I.graph.generate(t,colors,b['q'])
            check(name+f'/q{b["q"]}/independent-receipt',{x:r[x] for x in r},{x:reference[x] for x in r})
            check(name+f'/q{b["q"]}/all-original-residuals',all(I.graph.validate_emission(t,colors,b['q'],o) for o in r['outputs']),True)
            check(name+f'/q{b["q"]}/all-parent-occurrences',[I.whole_membership(t,P,o['partition']) for o in r['outputs']],b['preservation'])
            check(name+f'/q{b["q"]}/restriction-transport',[I.unchanged_restrictions(t,P,o['partition']) for o in r['outputs']],b['preservation'])
            if k in cache:check(name+'/same-actual-call',cache[k],r)
            cache[k]=r;owntraces.append({'id':name,'q':b['q'],'trace':reference['trace'],'trace_origin':'unchanged independent pointer instrument; actual Lean cut list checked separately'})
    for f in E['malformed_sources']:
        check('malformed/'+f['id'],actual['MALFORMED:'+f['id']],original_guards(f['tree'],f['parents']))
        check('malformed/'+f['id']+'/proper-source',all(actual['MALFORMED:'+f['id']]),f['proper_source'])
        if 'generator_refusal' in f:
            r=actual['DUPLICATE-REFUSAL'];check('duplicate-original-refusal',r['refusals'],[f['generator_refusal']]);check('duplicate-original-empty',r['outputs'],[])
            cache[configkey(f['tree'],{x:0 for x in I.graph.syntax_leaves(f['tree'])},9)]=r
    check('complete-readout-denominator',len(actual),11*4+20+7+1)
    out={'status':'PASS_ACTUAL_COMPILED_FROZEN_READOUT','source_sha256':R.sha(source),'build':build,'comparisons':len(checks),'checks':checks,'actual':actual,'generate_cache':cache,'independent_traces':owntraces,'expectations_v2_sha256':R.sha(PRE/'EXPECTATIONS-v2.json'),'model_diagnosed_exact_list_expectations':['root-nonclade-A','root-nonclade-C'],'all_main_milestones':'OPEN','replication_count_added':0}
    dest=R.ROOT/'research/rmaf/results/algorithm-kept-parent-fresh-review-readout-v1.json';dest.write_text(json.dumps(out,indent=2)+'\n');print(out['status'],out['comparisons'],len(cache))
if __name__=='__main__':main()
