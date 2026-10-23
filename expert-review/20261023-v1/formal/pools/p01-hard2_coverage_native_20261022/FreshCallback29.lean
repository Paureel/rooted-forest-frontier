import ControlFlowV4
import BOForest
import GroupForwardProof
import GroupForward
import GroupRestriction
import OriginalReconstruction
import LocalSlots
import Optimality01
import LocalPaid08
import ForestComplete12
import ForestSkinny06
import ForestProgram
import FreshParentFacts25
open RMAF Universal233 RestrictionBridge
namespace FreshOrdinaryBridge
theorem paid_bounded_IH (outer r : Nat) (hstrict : r<outer)
    (below : IndependentReconstruction.BelowBudget outer) :
    ForestMinCompletion.LocalOrdinaryIH r (IndependentReconstruction.OwnPaid outer) := by
  constructor
  · intro T S b F hb hp hF
    have hbo : b<outer := by omega
    have exactBelow:=below b hbo T S hp
    have paid : IndependentReconstruction.OwnPaid outer T S b=OrdinaryDispatch.FastOrdinary.solve b T S := by
      simp only [IndependentReconstruction.OwnPaid,dif_pos hbo]
    rw [paid] at hF
    rw [hF] at exactBelow
    exact exactBelow
  · intro T S b G hb hp hG hcost
    have hbo : b<outer := by omega
    have exactBelow:=below b hbo T S hp
    cases hs : OrdinaryDispatch.FastOrdinary.solve b T S with
    | none =>
      rw [hs] at exactBelow
      have impossible:=exactBelow G hG
      omega
    | some F =>
      refine ⟨F,?_⟩
      simp only [IndependentReconstruction.OwnPaid,dif_pos hbo,hs]

theorem singleton_state_proper (T S : Tree) (hp : DepthOne.proper T S=true) :
    ForestState.proper (some T) [S]=true := by
  obtain ⟨nt,ns,labels⟩:=(DepthOne.proper_iff T S).mp hp
  have one : partitionCheck (leaves S) [leaves S]=true := by
    simp only [partitionCheck,List.all_cons,List.all_nil,List.flatten_cons,List.flatten_nil,
      List.append_nil,Bool.and_true,Bool.and_eq_true,Bool.not_eq_true',
      List.isEmpty_eq_false_iff,List.all_eq_true,beq_iff_eq,List.contains_iff_mem]
    exact ⟨⟨leaves_nonempty S,fun x hx=>ns.count_of_mem hx⟩,fun x hx=>hx⟩
  have hpart : partitionCheck (leaves T) [leaves S]=true :=
    (partition_labels_congr (leaves T) (leaves S) [leaves S] (fun _=>labels.mem_iff)).2 one
  simp only [ForestState.proper,ForestState.labels,List.map_cons,List.map_nil,
    Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨by simp [nt],hpart⟩

theorem singleton_callback_exact (outer r : Nat) (hstrict : r<outer)
    (below : IndependentReconstruction.BelowBudget outer) (T S : Tree)
    (hp : DepthOne.proper T S=true) :
    OrdinaryDispatch.QueryExact T S r
      (BothBad.asTree (GenericForest.solve (IndependentReconstruction.OwnPaid outer)) T S r) := by
  have ho:=paid_bounded_IH outer r hstrict below
  have stateProper:=singleton_state_proper T S hp
  have complete (G : List (List Nat)) (hG : agreement T S G=true) (hcost : G.length-1≤r) :
      ∃F,GenericForest.solve (IndependentReconstruction.OwnPaid outer) (some T) [S] r=some F ∧ F.length≤G.length := by
    exact PaidInstanceForest.forest_complete_local r (IndependentReconstruction.OwnPaid outer) ho r
      (Nat.le_refl r) (some T) [S] G
      ((ForestState.initial_state_agreement_iff T S G stateProper).2 hG)
      (by simpa only [ForestState.additionalCost,List.length_cons,List.length_nil] using hcost)
  change OrdinaryDispatch.QueryExact T S r
    (GenericForest.solve (IndependentReconstruction.OwnPaid outer) (some T) [S] r)
  cases he : GenericForest.solve (IndependentReconstruction.OwnPaid outer) (some T) [S] r with
  | none =>
    intro G hG
    by_cases feasible : G.length-1≤r
    · obtain ⟨F,hF,_⟩:=complete G hG feasible
      rw [he] at hF
      cases hF
    · omega
  | some F =>
    obtain ⟨hag,hbudget⟩:=GenericForest.solve_sound (IndependentReconstruction.OwnPaid outer) (some T) [S] r F he
    have hAF:=(ForestState.initial_state_agreement_iff T S F stateProper).1 hag
    have cost : F.length-1≤r := by
      simpa only [ForestState.additionalCost,List.length_cons,List.length_nil] using hbudget
    refine ⟨hAF,cost,?_⟩
    intro G hG
    by_cases feasible : G.length-1≤r
    · obtain ⟨H,hH,hmin⟩:=complete G hG feasible
      have hFH : F=H := Option.some.inj (he.symm.trans hH)
      simpa only [hFH] using hmin
    · omega
end FreshOrdinaryBridge

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshOrdinaryBridge.paid_bounded_IH
#print axioms FreshOrdinaryBridge.paid_bounded_IH
#check @FreshOrdinaryBridge.singleton_state_proper
#print axioms FreshOrdinaryBridge.singleton_state_proper
#check @FreshOrdinaryBridge.singleton_callback_exact
#print axioms FreshOrdinaryBridge.singleton_callback_exact
