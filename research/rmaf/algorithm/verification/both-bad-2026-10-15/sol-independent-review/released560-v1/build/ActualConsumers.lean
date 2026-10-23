import ResidualConsumer
import ConsumerControls
namespace OutputState.ActualControls
open RMAF RestrictionBridge ForestState ForestGroups VertexGeometry BinaryExchange
open Universal233 Universal233.CoreProgram Universal233.PairAssembly
open Universal233.BinaryCheap.Controls
-- Postproof development contact: frozen binary-cheap compact actual fixture.
def actualO : Output := ⟨[[5,6],[7,8],[1,2,3,4],[9]],[[true,false],[true,false,true,true],[false]]⟩
theorem actual_member : actualO ∈ sideOutputs s a b d 7 := by decide
theorem actual_noncanonical_order : (sourceForest s actualO.partition).map leaves =
    [[5,6],[7,8],[1,2,3,4],[9]] ∧
    (owned (sourceForest s actualO.partition) b).length = 2 := by decide

theorem actual_equivalence (F : List (List Nat)) :
    agrees (some t) (sourceForest s actualO.partition) F = true ↔
      agreement t s F = true ∧ RestrictionBridge.Refines F actualO.partition := by
  have hgen : actualO ∈ (generate s (Assembly.taggedColor a b (fun _ => 0) (sideColor d) (fun _ => 0)) 7).outputs := actual_member
  exact (generated_source_bridge t s _ 7 actualO hgen (by decide) (by decide)
    (fun x => (same_labels x).symm)).2.2.1 F

theorem actual_group_local_certificates : ∃ sa ta p,
    restrict a s = some sa ∧ restrict a t = some ta ∧
    KeptParent.OriginalLocalOneCut s t a ⟨DepthOne.forest sa (some p),[p]⟩ ∧
    ∃ aa cc, restrict a s = some aa ∧ restrict c s = some cc ∧
      agrees (localTarget (some t) a) [aa] (DepthOne.forest sa (some p)) = true ∧
      additionalCost [aa] (DepthOne.forest sa (some p)) = 1 ∧
      agrees (localTarget (some t) c) [cc] [c] = true ∧ additionalCost [cc] [c] = 0 := by
  obtain ⟨sa,ta,p,hrs,hrt,hfound,hcert,hothers⟩ := control_selected_local_and_forall_opposite
  have hd : PairGeometry.descendants t [false,false] = d := by decide
  have member : actualO ∈ sideOutputs s a b (PairGeometry.descendants t [false,false]) 7 := by
    rw [hd]; exact actual_member
  have safe := hothers 7 actualO member
  obtain ⟨aa,cc,hra,hrc,hla,hlc,ownA,ownC,perm,hproper,hclear⟩ :=
    opposite_grouping t s a b c d _ actualO 7 (by decide) (by decide)
      (fun x => (same_labels x).symm) control_source.1 actual_member safe
  obtain ⟨ha,ca,hc,ccost⟩ := opposite_local_certificates t s a b c _ actualO aa cc
    (by decide) (by decide) (fun x => (same_labels x).symm) control_source.1 safe hra hrc control_bad.2.2
  exact ⟨sa,ta,p,hrs,hrt,hcert,aa,cc,hra,hrc,ha,ca,hc,ccost⟩

private theorem actual_private_origin : (8 : Nat) = 8 := rfl
theorem actual_private_origin_export : (8 : Nat) = 8 := actual_private_origin
end OutputState.ActualControls
