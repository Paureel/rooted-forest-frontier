#!/usr/bin/env python3
"""One-shot kept-parent development controls; literal Lean path retained separately."""
from pathlib import Path
import importlib.util, json, hashlib, time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
HAND=HERE.parent.parent/'pair_case/cheap_high/x0/sol-handoff-v1'
spec=importlib.util.spec_from_file_location('x0',HAND/'payload/sol-evaluator-v1.py')
x0=importlib.util.module_from_spec(spec); spec.loader.exec_module(x0)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def kept(o,A):return sum(set(k)==set(A) for k in o['partition'])==1
def lt(t):
    return f'(.leaf {t})' if isinstance(t,int) else f'(.node {lt(t[0])} {lt(t[1])})'
def ln(xs):return '['+', '.join(map(str,xs))+']'
fixtures=json.loads((HAND/'payload/sol-fixtures-v1.json').read_text())['fixtures']
outscope=json.loads((HAND/'payload/sol-outscope-plant-v1.json').read_text())
configs=[]; rows=[]; start=time.monotonic()
for f in fixtures+[outscope]:
 A,B,C=f['P']; graph=x0.Graph(f['S'])
 for mode in ['sector','arbitrary'] if f is not outscope else ['sector']:
  col={x:(0 if x in A else 3*(0 if x in x0.Graph(f['T']).desc[f['edge']] else 1)+1 if x in B else 2) for x in graph.labels}
  if mode=='arbitrary':col={x:(3*(x%3)+1 if x in B else col[x]) for x in graph.labels}
  for q in range(f['q']+1):
   r=x0.generate(f['S'],col,q)
   a=[kept(o,A) for o in r['outputs']];c=[kept(o,C) for o in r['outputs']]
   row={'id':f['id']+'/'+mode,'q':q,'source_partition':x0.proper(graph.labels,f['P']),'source_embeddings':graph.disjoint(f['P']),'receipt':r,'kept_A':a,'kept_C':c}
   rows.append(row);configs.append((row['id'],f['S'],f['P'],col,q))
   if f is not outscope:assert row['source_partition'] and row['source_embeddings'] and all(a) and all(c)
   elif q==f['q']:assert not row['source_embeddings'] and a.count(False)==2
A,B,C=fixtures[0]['P'];S=fixtures[0]['S'];g=x0.Graph(S)
wrong=x0.generate(S,{x:0 for x in g.labels},7)
assert len(wrong['outputs'])==1 and not kept(wrong['outputs'][0],A)
assert not x0.generate([1,1],{1:0},3)['outputs']
assert x0.generate([1,1],{1:0},3)['refusals']==['duplicate original label']
assert not x0.proper([1,1],[[1]])
assert not rows[0]['receipt']['outputs']
clean=next(row for row in rows if row['receipt']['outputs'])['receipt']['outputs'][0]
cleanA=fixtures[0]['P'][0]
assert kept(clean,cleanA)
corrupt={'partition':[list(b) for b in clean['partition']]}
for b in corrupt['partition']:
 if set(b)==set(cleanA):b.pop();break
assert not kept(corrupt,cleanA)
rc=x0.generate([[0,1],[2,3]],{x:x%2 for x in range(4)},3)
assert x0.canon([[0],[1],[2],[3]]) not in [x0.canon(o['partition']) for o in rc['outputs']]
result={'schema':'universal233-kept-controls/v1','seconds':time.monotonic()-start,'controls_passed':7,'config_count':len(rows),'literal_outputs':sum(len(r['receipt']['outputs']) for r in rows),'sources':{'pin':sha(HERE/'CONTROLS-PIN-v1.json'),'evaluator':sha(HAND/'payload/sol-evaluator-v1.py'),'core':sha(HERE.parent/'core/CoreProgram.lean')},'rows':rows,'wrong_global_zero':wrong,'denominator':len(rows)}
(ROOT/'research/rmaf/results/algorithm-universal233-kept-controls-v1.json').write_text(json.dumps(result,indent=2)+'\n')
lean=['import Lean','import CoreProgram','open RMAF Universal233.CoreProgram Lean',
'def configs : List (String × Tree × List (List Nat) × List (Nat × Nat) × Nat) := [']
for i,(name,t,P,col,q) in enumerate(configs):
 lean.append(f'({json.dumps(name)}, {lt(t)}, [{", ".join(ln(b) for b in P)}], [{", ".join(f"({x}, {v})" for x,v in col.items())}], {q})'+(',' if i+1<len(configs) else ''))
lean+= [']',
'def addr (p : Vertex) : String := String.join (p.map (fun b => if b then "1" else "0"))',
'def outputJson (o : Output) : Json := Json.mkObj [("partition", toJson o.partition), ("sourceCuts", toJson (o.sourceCuts.map addr))]',
'def main : IO Unit := do',
'  for (name,t,P,colors,q) in configs do',
'    let col := fun x => ((colors.find? (fun z => z.1 == x)).map Prod.snd).getD 99',
'    let r := generate t col q',
'    let j := Json.mkObj [("id",toJson name),("q",toJson q),("source_partition",toJson (partitionCheck (leaves t) P)), ("source_embeddings",toJson (pairwiseEmbeddings t P)), ("outputs", Json.arr (r.outputs.map outputJson).toArray), ("refusals",toJson r.refusals), ("visited",toJson r.visited), ("childAttempts",toJson r.childAttempts), ("pruned",toJson r.pruned)]',
'    IO.println j.compress']
(HERE/'LiteralControls.lean').write_text('\n'.join(lean)+'\n')
print(json.dumps({k:result[k] for k in ['seconds','controls_passed','config_count','literal_outputs']}))
