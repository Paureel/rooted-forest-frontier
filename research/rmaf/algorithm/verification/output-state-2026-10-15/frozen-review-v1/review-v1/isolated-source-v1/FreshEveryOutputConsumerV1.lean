import FreshActualReadoutsV2
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
