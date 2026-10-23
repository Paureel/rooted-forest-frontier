import G0Native
import PaidRequests
import CurrentQuery
import GroupCost
namespace ActualRule5Caller
open RMAF Universal233 Universal233.Rule5Case322 Universal233.Rule5PaidSelector
open Universal233.Case322PaidGuard VertexGeometry

theorem refinement_size (labels : List Nat) (F P : List (List Nat))
    (hF : partitionCheck labels F = true) (hP : partitionCheck labels P = true)
    (ref : Refines F P) : P.length ≤ F.length := by
  have positive : ∀ U ∈ P, 0 < (RestrictionBridge.family U F).length := by
    intro U hu
    exact List.length_pos_iff.mpr
      (RestrictionBridge.family_nonempty labels F P hF hP ref U hu)
  have hsum := RestrictionBridge.sum_sub_one P
    (fun U => (RestrictionBridge.family U F).length) positive
  have htotal := RestrictionBridge.total_family_length labels F P hF hP ref
  omega

theorem guarded_affordable_from_survival {T S : Tree} (D : LiteralGeometry T S)
    (q : Nat) (G : List (List Nat)) (hG : agreement T S G = true)
    (budget : G.length - 1 ≤ q) :
    ∃ c ∈ guardedPlan D, paid c ≤ q ∧
      ∃ H, agreement T S H = true ∧ H.length ≤ G.length ∧
        Refines H c.partition ∧ H.length - c.partition.length ≤ q - paid c := by
  obtain ⟨c,member,H,hH,least,ref⟩ := RootGenericG0.generic_g0_survival T S D G hG
  have guard := (List.mem_filter.mp member).2
  have parts := guard_current_parts guard
  have checked : partitionCheck (leaves (current T S c)) H = true := by
    have both := BinaryExchange.agreement_parts T S H hH
    cases role : c.role with
    | source => simpa [current,role] using both.2.1
    | target => simpa [current,role] using both.1
  have size := refinement_size _ H c.partition checked parts.1 ref
  refine ⟨c,member,?_,H,hH,least,ref,?_⟩ <;> omega

theorem requests_cover_from_g0 {T S : Tree} (D : LiteralGeometry T S)
    (q : Nat) (G : List (List Nat)) (hG : agreement T S G = true)
    (budget : G.length - 1 ≤ q) :
    ∃ Q ∈ requests D q,
      ∃ H, ForestState.agrees (some Q.target) Q.sources H = true ∧
        H.length ≤ G.length ∧ ForestState.additionalCost Q.sources H ≤ Q.residual := by
  obtain ⟨c,member,affordable,H,hH,least,ref,residual⟩ :=
    guarded_affordable_from_survival D q G hG budget
  have guard := (List.mem_filter.mp member).2
  let Q : PaidRequest := ⟨c,opposite T S c,sourceForest T S c,q-paid c⟩
  have pick : requestFor T S q c = some Q := by simp [requestFor,affordable,Q]
  refine ⟨Q,List.mem_filterMap.mpr ⟨c,member,pick⟩,H,?_,least,?_⟩
  · exact (full_state_iff D c guard H).mpr ⟨hH,ref⟩
  · change ForestState.additionalCost (sourceForest T S c) H ≤ q-paid c
    rw [full_state_cost D c guard H]
    exact residual

#print axioms guarded_affordable_from_survival
#print axioms requests_cover_from_g0
end ActualRule5Caller
