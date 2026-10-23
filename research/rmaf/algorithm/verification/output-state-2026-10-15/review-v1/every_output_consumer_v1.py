from pathlib import Path
import json,subprocess,os,time,importlib.util,sys
from collections import Counter,deque
H=Path(__file__).resolve().parent;R=next(p for p in H.parents if (p/'bootloops-lean').is_file());F=H/'isolated-source-v1';sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('own_graph',H.parent/'frozen-ready-v1/frozen-inputs-v1/own_paircase_dependency.py');g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
s='''import FreshActualReadoutsV2
namespace FreshEveryOutputConsumer
open RMAF RestrictionBridge ForestState ForestGroups OutputState
open Universal233 Universal233.CoreProgram Universal233.PairAssembly
open Universal233.BinaryCheap.Controls
open FreshOutputReadouts
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
/-- All actual outputs, all source budgets, with no favorable-output filter.
Only the exact child's solver contract remains supplied. -/
theorem every_actual_output_conditional_consumer :
 ∃ aout : Output, KeptParent.OriginalLocalOneCut s t a aout ∧
 ∀ q0 o, o ∈ sideOutputs s a b d q0 →
   BinaryCheap.OppositeSafe s t a b c aout o ∧
   ∀ (solve : Option Tree → List Tree → Nat → Option (List (List Nat)))
     (q : Nat) (FB : List (List Nat)),
     0 < q →
     ResidualSolverContract solve (localTarget (some t) b) (owned (sourceForest s o.partition) b) (q-1) →
     solve (localTarget (some t) b) (owned (sourceForest s o.partition) b) (q-1) = some FB →
     let F := aout.partition ++ FB ++ [c]
     agrees (some t) (sourceForest s o.partition) F = true ∧
     agreement t s F = true ∧ Refines F o.partition ∧
     additionalCost (sourceForest s o.partition) F = 1+additionalCost (owned (sourceForest s o.partition) b) FB ∧
     additionalCost (sourceForest s o.partition) F ≤ q ∧ F.length-o.partition.length ≤ q := by
 obtain ⟨sa,ta,p,hrs,hrt,hfound,hcert,hothers⟩ := control_selected_local_and_forall_opposite
 let aout : Output := ⟨DepthOne.forest sa (some p),[p]⟩
 refine ⟨aout,hcert,?_⟩
 intro q0 o ho
 have hd : PairGeometry.descendants t [false,false] = d := by decide
 have hos : o ∈ sideOutputs s a b (PairGeometry.descendants t [false,false]) q0 := by simpa only [hd] using ho
 have safe := hothers q0 o hos
 refine ⟨safe,?_⟩
 intro solve q FB positive IH query
 exact OutputState.every_opposite_residual_query solve t s a b c d aout o q0 q FB
   (by decide) (by decide) (fun x => (same_labels x).symm) control_source.1 ho safe
   (by decide) positive IH query

def sourceCutsJson (ps : List RMAF.Vertex) : Lean.Json := Lean.toJson ps

def allOutputReadouts (q : Nat) : IO Unit := do
 let outputs := sideOutputs s a b d q
 let objects := outputs.map fun o =>
  let ss := sourceForest s o.partition
  let aa := owned ss a
  let bs := owned ss b
  let cc := owned ss c
  Lean.Json.mkObj [("partition",Lean.toJson o.partition),("sourceCuts",sourceCutsJson o.sourceCuts),
   ("member",Lean.toJson (outputs.contains o)),("sources",forestJson ss),
   ("source_checked",Lean.toJson (partitionCheck (leaves s) o.partition)),
   ("source_clear",Lean.toJson (pairwiseEmbeddings s o.partition)),
   ("target_clear",Lean.toJson (pairwiseEmbeddings t o.partition)),
   ("source_count",Lean.toJson ss.length),("source_proper",Lean.toJson (proper (some t) ss)),
   ("refines_parents",Lean.toJson (freshRefines o.partition [a,b,c])),
   ("A_sources",forestJson aa),("B_sources",forestJson bs),("C_sources",forestJson cc),
   ("B_internal_target_clear",Lean.toJson (pairwiseEmbeddings t (bs.map leaves))),
   ("source_permutation",Lean.toJson (decide (ss.Perm (aa++bs++cc)))),
   ("priority_clear",Lean.toJson (decide (aa.length=1) && aa.all (fun z => priorityBool t z bs cc)))]
 printObj ("allOutputs.q"++toString q) [("q",Lean.toJson q),("outputs",Lean.Json.arr objects.toArray)]
#eval printObj "actual_fixture" [("S",treeJson s),("T",treeJson t),("A",Lean.toJson a),("B",Lean.toJson b),("C",Lean.toJson c),("D",Lean.toJson d)]
#eval (List.range 8).forM allOutputReadouts
#eval do
 match restrict a s,restrict a t with
 | some sa,some ta =>
   match DepthOne.pretest01 ta sa with
   | .found p =>
     let fa := DepthOne.forest sa p
     printObj "actual_local_A" [("S",treeJson sa),("T",treeJson ta),("cut",Lean.toJson p),("F",Lean.toJson fa),
       ("state",Lean.toJson (agrees (some ta) [sa] fa)),("original",Lean.toJson (agreement ta sa fa)),("cost",Lean.toJson (additionalCost [sa] fa))]
   | _ => throw (IO.userError "actual local A pretest did not find witness")
 | _,_ => throw (IO.userError "actual local A source/target restriction missing")
#print axioms every_actual_output_conditional_consumer
end FreshEveryOutputConsumer
'''
(F/'FreshEveryOutputConsumerV1.lean').write_text(s);env=os.environ.copy();env['LEAN_PATH']=str(F);start=time.monotonic();p=subprocess.run([str(R/'bootloops-lean'),'-o','FreshEveryOutputConsumerV1.olean','FreshEveryOutputConsumerV1.lean'],cwd=F,env=env,capture_output=True,text=True,timeout=30);log=p.stdout+p.stderr;(F/'FreshEveryOutputConsumerV1.log').write_text(log);assert p.returncode==0,log[-6000:]
reads={}
for line in log.splitlines():
 if line.startswith('READ|'):
  _,key,data=line.split('|',2);reads[key]=json.loads(data)
fixture=reads['actual_fixture'];S,T=g.Original(fixture['S']),g.Original(fixture['T']);A,B,C,D=fixture['A'],fixture['B'],fixture['C'],fixture['D'];banks=[];count=0;internal_overlaps=0

def residual_components(tree,cuts):
 addresses=[''.join('1' if b else '0' for b in p) for p in cuts]
 assert len(addresses)==len(set(addresses)) and all(p and (p[:-1],p) in tree.edges for p in addresses)
 graph={v:set(ws) for v,ws in tree.graph.items()}
 for p in addresses:graph[p].remove(p[:-1]);graph[p[:-1]].remove(p)
 seen=set();parts=[]
 for root in sorted(graph):
  if root in seen:continue
  seen.add(root);todo=[root];block=[]
  while todo:
   v=todo.pop()
   if v in tree.leaf_at:block.append(tree.leaf_at[v])
   for w in graph[v]-seen:seen.add(w);todo.append(w)
  assert block,('unlabelled_residual_component',root)
  parts.append(block)
 assert len(parts)==len(cuts)+1
 return g.canon_partition(parts)

for q in range(8):
 bank=reads['allOutputs.q'+str(q)];assert bank['q']==q;rows=[]
 for o in bank['outputs']:
  count+=1;Q=o['partition'];ss=[u for U in Q if (u:=g.raw_restrict(S.tree,U)) is not None]
  aa=[u for u in ss if set(g.Original(u).labels)<=set(A)];bb=[u for u in ss if set(g.Original(u).labels)<=set(B)];cc=[u for u in ss if set(g.Original(u).labels)<=set(C)]
  assert o['member'] and o['source_checked'] and o['source_clear'] and o['source_proper'] and o['refines_parents'] and o['priority_clear'] and o['source_permutation']
  assert g.partition_check(S.labels,Q) and S.embedding_disjoint(Q) and g.refines(Q,[A,B,C])
  assert o['sources']==json.loads(json.dumps(ss)) and o['source_count']==len(Q)
  assert o['A_sources']==json.loads(json.dumps(aa)) and o['B_sources']==json.loads(json.dumps(bb)) and o['C_sources']==json.loads(json.dumps(cc))
  assert aa==[g.raw_restrict(S.tree,A)] and cc==[g.raw_restrict(S.tree,C)]
  assert Counter(map(repr,ss))==Counter(map(repr,aa+bb+cc))
  for u,v in [(a,b) for a in aa for b in bb+cc]+[(b,c) for b in bb for c in cc]:assert not T.hull(frozenset(g.Original(u).labels))&T.hull(frozenset(g.Original(v).labels))
  internal=T.embedding_disjoint([g.Original(x).labels for x in bb]);assert internal==o['B_internal_target_clear']
  if not internal:internal_overlaps+=1
  assert residual_components(S,o['sourceCuts'])==g.canon_partition(Q)
  assert len(o['sourceCuts'])<=q
  rows.append({'partition':Q,'sourceCuts':o['sourceCuts'],'independent_original_residual_graph_matches':True,'source_valid':True,'all_owned_B_pieces_checked':len(bb),'B_internal_target_clear':internal})
 banks.append({'q':q,'output_denominator':len(bank['outputs']),'all_outputs':rows})
local=reads['actual_local_A'];LS,LT=g.Original(local['S']),g.Original(local['T']);assert local['cut'] is not None and local['state'] and local['original'] and local['cost']==1
assert residual_components(LS,[local['cut']])==g.canon_partition(local['F']) and g.agrees(LS,LT,local['F'])
out={'verdict':'PASS_ALL_OUTPUTS_SCOPED_CONSUMER_AND_ORIGINAL_GRAPH_READOUTS','seconds':time.monotonic()-start,'proven_consumer':'FreshEveryOutputConsumer.every_actual_output_conditional_consumer','universal_scope':'all q0 and every actual sideOutputs member of the explicit released nine-label fixture; exact future child contract remains supplied','finite_queries':8,'finite_output_denominator':count,'internal_target_overlap_outputs':internal_overlaps,'banks':banks,'fixture':fixture,'local_A':local,'post_candidate_contact_supplement':True,'preproof_control_credit':False,'full_recursive_solver_implemented':False,'all_main_milestones':'OPEN'}
(R/'research/rmaf/results/algorithm-output-state-fresh-every-output-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['verdict','seconds','finite_queries','finite_output_denominator','internal_target_overlap_outputs']}))
