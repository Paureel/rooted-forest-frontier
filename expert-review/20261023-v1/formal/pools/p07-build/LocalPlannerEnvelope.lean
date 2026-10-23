import LocalExecutionBounds
namespace OrdinaryDispatch.Hard2SourceWork.LocalDispatchEnvelope
open RMAF Universal233 WholeSourceWork CoreWork GenericForest.CheckCorrespondence
open Universal233.BothBad Universal233.BinaryCheap Universal233.RankConsumer

theorem cheapPlan_length (S T : Tree) (A B C D : List Nat) (q : Nat)
 (cheap opposite : List CoreProgram.Output) :
 (cheapPlan S T A B C D q cheap opposite).length≤cheap.length+opposite.length := by
 have ca:=entries_length q .ordinary cheap
 have cf:=entries_length q .full opposite
 have cr (F : List (List Nat)):=entries_length q (.retained A B C F) opposite
 simp only [cheapPlan]
 split
 · cases h:knownOne T S A with
   | none=>simp
   | some F=>have c:=cr F;simp only [List.length_append];omega
 · simp only [List.length_append];omega

theorem generate_length (S : Tree) (color : Nat→Nat) (r q : Nat) (rq:r≤q) :
 (CoreProgram.generate S color r).outputs.length≤3*2^(q+1) := by
 have c:=generate_output_count S color r
 have p:=Nat.pow_le_pow_right (show 1≤2 by decide)
  (show min r ((leaves S).length-1)+1≤q+1 by omega)
 have m:=Nat.mul_le_mul_left 3 p
 omega

theorem reuse_length (S : Tree) (color : Nat→Nat) (probe : List CoreProgram.Output) (q : Nat)
 (len:probe.length≤3*2^(q+1)) : (reuse S color probe q).length≤3*2^(q+1) := by
 simp only [reuse]
 split
 · exact generate_length S color q q (Nat.le_refl _)
 · exact len

/-- The actual planner produces at most the sum of its two actual output lists.
 Probe reuse and entry refusal preserve this bound without deduplication. -/
theorem plan_length (S T : Tree) (A B C D : List Nat) (q : Nat) :
 (bothBadPlanMeter S T A B C D q).value.length≤6*2^(q+1) := by
 rw [bothBadPlanMeter_value]
 by_cases low:q<3
 · simp only [plan,low,ite_true,List.length_nil];omega
 · have a:=generate_length S (cheapColor A B D) 3 q (by omega)
   have b:=generate_length S (cheapColor B A D) 3 q (by omega)
   have x:=generate_length S (cheapColor A B D) q q (Nat.le_refl _)
   have y:=generate_length S (cheapColor B A D) q q (Nat.le_refl _)
   have ra:=reuse_length S (cheapColor A B D) _ q a
   have rb:=reuse_length S (cheapColor B A D) _ q b
   have ca:=cheapPlan_length S T A B C D q
    (CoreProgram.generate S (cheapColor A B D) 3).outputs
    (reuse S (cheapColor B A D) (CoreProgram.generate S (cheapColor B A D) 3).outputs q)
   have cb:=cheapPlan_length S T B A C D q
    (CoreProgram.generate S (cheapColor B A D) 3).outputs
    (reuse S (cheapColor A B D) (CoreProgram.generate S (cheapColor A B D) 3).outputs q)
   have ent:=entries_length q .full
    ((CoreProgram.generate S (cheapColor A B D) q).outputs++(CoreProgram.generate S (cheapColor B A D) q).outputs)
   simp only [List.length_append] at ent
   by_cases ha:(CoreProgram.generate S (cheapColor A B D) 3).outputs.isEmpty=true
   · by_cases hb:(CoreProgram.generate S (cheapColor B A D) 3).outputs.isEmpty=true
     all_goals simp only [plan,fourProbe,low,ha,hb,Bool.false_eq_true,ite_true,ite_false];omega
   · simp only [plan,fourProbe,low,ha,Bool.false_eq_true,ite_false];omega

def plannerExecutionCoefficient (N Q : Nat) := bothBadPlanCoefficient N Q+6*executionPolynomial N

/-- A concrete sum of the unchanged actual planner and local execution meters.
 All residual callback computation is separate in the frozen source split. -/
theorem planner_execution_bound (actual : GenericForest.FrontierWork.Ordinary) (S T : Tree)
 (A B C D : List Nat) (q N Q : Nat) (three:3≤N) (tn:treeNodes T≤N) (sn:treeNodes S≤N)
 (al:A.length≤N) (bl:B.length≤N) (cl:C.length≤N) (dl:D.length≤N) (budget:q≤Q) :
 (bothBadPlanMeter S T A B C D q).work+
 (bothBadExecuteLocalSource actual T S q (bothBadPlanMeter S T A B C D q).value).work≤
 plannerExecutionCoefficient N Q*2^(q+1)+2 := by
 have p:=bothBadPlanMeter_bound S T A B C D q N Q tn sn al bl dl budget
 have e:=actual_plan_execute_bound actual S T A B C D q N three tn sn al bl cl
 have l:=plan_length S T A B C D q
 have m:=Nat.mul_le_mul_left (executionPolynomial N) l
 simp only [plannerExecutionCoefficient,Nat.add_mul,Nat.mul_assoc,Nat.mul_left_comm] at *
 omega

/-- The exponent is the original planner q, including both fixed probes.
 This is an author source-work component, not whole-algorithm acceptance. -/
theorem planner_execution_weighted (actual : GenericForest.FrontierWork.Ordinary) (S T : Tree)
 (A B C D : List Nat) (q N Q : Nat) (three:3≤N) (tn:treeNodes T≤N) (sn:treeNodes S≤N)
 (al:A.length≤N) (bl:B.length≤N) (cl:C.length≤N) (dl:D.length≤N) (budget:q≤Q) :
 (((bothBadPlanMeter S T A B C D q).work+
 (bothBadExecuteLocalSource actual T S q (bothBadPlanMeter S T A B C D q).value).work:Nat):Rat)≤
 ((2*plannerExecutionCoefficient N Q+6:Nat):Rat)*Rule5ActualTrace.base^q := by
 have h:=planner_execution_bound actual S T A B C D q N Q three tn sn al bl cl dl budget
 have hn:(bothBadPlanMeter S T A B C D q).work+
  (bothBadExecuteLocalSource actual T S q (bothBadPlanMeter S T A B C D q).value).work≤
  plannerExecutionCoefficient N Q*2^(q+1)+6:=by omega
 exact Rat.le_trans (Rat.natCast_le_natCast.2 hn) (binary_prefix_absorb _ q)

theorem semantic_partition_caps (S : Tree) (A B C : List Nat) (N : Nat)
 (hs:(leaves S).Nodup) (sn:treeNodes S≤N) (hp:partitionCheck (leaves S) [A,B,C]=true) :
 A.length≤N ∧ B.length≤N ∧ C.length≤N := by
 have p:=(FinalCutRecovery.checked_flatten_perm S [A,B,C] hs hp).length_eq
 have l:=leaves_nodes S
 simp only [List.flatten_cons,List.flatten_nil,List.append_nil,List.length_append] at p
 omega

theorem semantic_planner_execution_weighted (actual : GenericForest.FrontierWork.Ordinary) (S T : Tree)
 (A B C D : List Nat) (q N Q : Nat) (three:3≤N) (tn:treeNodes T≤N) (sn:treeNodes S≤N)
 (hs:(leaves S).Nodup) (hp:partitionCheck (leaves S) [A,B,C]=true)
 (dl:D.length≤N) (budget:q≤Q) :
 (((bothBadPlanMeter S T A B C D q).work+
 (bothBadExecuteLocalSource actual T S q (bothBadPlanMeter S T A B C D q).value).work:Nat):Rat)≤
 ((2*plannerExecutionCoefficient N Q+6:Nat):Rat)*Rule5ActualTrace.base^q := by
 have caps:=semantic_partition_caps S A B C N hs sn hp
 exact planner_execution_weighted actual S T A B C D q N Q three tn sn caps.1 caps.2.1 caps.2.2 dl budget
end OrdinaryDispatch.Hard2SourceWork.LocalDispatchEnvelope
