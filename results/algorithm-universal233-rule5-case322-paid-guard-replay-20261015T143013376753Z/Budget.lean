import T1Boundary
namespace Universal233.CherryBranching
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent

def OriginalWithin (T S : Tree) (k : Nat) : Prop :=
 ∃ F, agreement T S F = true ∧ F.length-1 ≤ k

def ChildWithin (T S : Tree) (c : Child) (r : Nat) : Prop :=
 ∃ F, feasible T S c F ∧ F.length-c.partition.length ≤ r

/-- The executable remaining-budget refusal/return has the exact original
meaning whenever this literal child has its proved source partition/cost. -/
theorem remaining_correct {T S : Tree} {c : Child} (k : Nat)
 (hp : partitionCheck (leaves S) c.partition = true)
 (he : pairwiseEmbeddings S c.partition = true)
 (paid : c.paid+1 = c.partition.length) :
 (∃ F, feasible T S c F ∧ F.length-1 ≤ k) ↔
 ∃ r, remaining k c = some r ∧ ChildWithin T S c r := by
 constructor
 · rintro ⟨F,hF,hk⟩
   have hid := paid_budget_identity hp he paid hF
   have hpay : c.paid ≤ k := by omega
   exact ⟨k-c.paid,(budget_exact k c hpay).1,F,hF,by omega⟩
 · rintro ⟨r,hr,F,hF,hk⟩
   unfold remaining at hr
   split at hr
   · have heq : k-c.paid = r := Option.some.inj hr
     have hid := paid_budget_identity hp he paid hF
     exact ⟨F,hF,by omega⟩
   · contradiction

theorem pendant_checks {T S : Tree} {p : RMAF.Vertex} {a b : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S) (hc : CoreGraph.CherryAt T p a b) :
 partitionCheck (leaves S) (pendantChild S a b).partition = true ∧
 pairwiseEmbeddings S (pendantChild S a b).partition = true ∧
 (pendantChild S a b).paid+1 = (pendantChild S a b).partition.length := by
 have ha : a ∈ leaves S := (same a).1 (leafAt_label T _ a (cherry_left hc))
 exact ⟨pendant_partition_check hnS ha,source_embeddings hnS,(pendant_paid S a b).2.symm⟩

theorem endpoint_checks {T S : Tree} {p : RMAF.Vertex} {a b : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S) (hc : CoreGraph.CherryAt T p a b) :
 partitionCheck (leaves S) (singletonChild S a).partition = true ∧
 pairwiseEmbeddings S (singletonChild S a).partition = true ∧
 (singletonChild S a).paid+1 = (singletonChild S a).partition.length := by
 have ha : a ∈ leaves S := (same a).1 (leafAt_label T _ a (cherry_left hc))
 have hb : b ∈ leaves S := (same b).1 (leafAt_label T _ b (cherry_right hc))
 exact ⟨singleton_partition_check hnS ha hb (cherry_distinct hnT hc),singleton_source_embeddings hnS,rfl⟩

/-- Actual t1 budget decision using only the literal pendant child. A bounded
child solver may be substituted only via its own ChildWithin equivalence. -/
theorem actual_t1_decision {T S : Tree} {p : RMAF.Vertex} {a b : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (hc : CoreGraph.CherryAt T p a b) (one : (cuts S a b).length = 1) (k : Nat) :
 OriginalWithin T S k ↔
 ∃ r, remaining k (pendantChild S a b) = some r ∧ ChildWithin T S (pendantChild S a b) r := by
 obtain ⟨hp,he,paid⟩ := pendant_checks hnT hnS same hc
 rw [←remaining_correct k hp he paid]
 constructor
 · rintro ⟨F,hF,hk⟩
   obtain ⟨G,hG,hlen,href⟩ := actual_t1_pendant_exchange hnT hnS same hF hc one
   exact ⟨G,⟨hG,href⟩,by omega⟩
 · rintro ⟨F,hF,hk⟩; exact ⟨F,hF.1,hk⟩

/-- Local high branch decision with EXPLICIT exact bounded solver contracts.
The current result supplies child predicates; it supplies no recursive solver. -/
theorem actual_high_decision {T S : Tree} {p : RMAF.Vertex} {a b : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (hc : CoreGraph.CherryAt T p a b) (_high : 3 ≤ (cuts S a b).length) (k : Nat) :
 OriginalWithin T S k ↔
 ∃ c, c ∈ branches S a b ∧ ∃ F, feasible T S c F ∧ F.length-1 ≤ k := by
 constructor
 · rintro ⟨F,hF,hk⟩
   obtain ⟨c,hc',hf⟩ := ordinary_branches_cover hnS hF hc
   exact ⟨c,hc',F,hf,hk⟩
 · rintro ⟨c,hc',F,hF,hk⟩; exact ⟨F,hF.1,hk⟩
end Universal233.CherryBranching

namespace Universal233.CherryBranching
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent

theorem branch_checks {T S : Tree} {p : RMAF.Vertex} {a b : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S) (hc : CoreGraph.CherryAt T p a b)
 {c : Child} (hcm : c ∈ branches S a b) :
 partitionCheck (leaves S) c.partition = true ∧ pairwiseEmbeddings S c.partition = true ∧
 c.paid+1 = c.partition.length := by
 have hcases : c = singletonChild S a ∨ c = singletonChild S b ∨ c = pendantChild S a b := by
   simpa [branches] using hcm
 rcases hcases with rfl | rfl | rfl
 · exact endpoint_checks hnT hnS same hc
 · have ha : a ∈ leaves S := (same a).1 (leafAt_label T _ a (cherry_left hc))
   have hb : b ∈ leaves S := (same b).1 (leafAt_label T _ b (cherry_right hc))
   exact ⟨singleton_partition_check hnS hb ha (Ne.symm (cherry_distinct hnT hc)),
     singleton_source_embeddings hnS,rfl⟩
 · exact pendant_checks hnT hnS same hc

theorem actual_high_budget {T S : Tree} {p : RMAF.Vertex} {a b : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (hc : CoreGraph.CherryAt T p a b) (high : 3 ≤ (cuts S a b).length) (k : Nat) :
 OriginalWithin T S k ↔ ∃ c, c ∈ branches S a b ∧
 ∃ r, remaining k c = some r ∧ ChildWithin T S c r := by
 rw [actual_high_decision hnT hnS same hc high k]
 constructor
 · rintro ⟨c,hm,hF⟩
   obtain ⟨hp,he,paid⟩ := branch_checks hnT hnS same hc hm
   exact ⟨c,hm,(remaining_correct k hp he paid).1 hF⟩
 · rintro ⟨c,hm,hr⟩
   obtain ⟨hp,he,paid⟩ := branch_checks hnT hnS same hc hm
   exact ⟨c,hm,(remaining_correct k hp he paid).2 hr⟩

theorem actual_t1_two_budget {T S : Tree} {p : RMAF.Vertex} {a b : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (hc : CoreGraph.CherryAt T p a b) (one : (cuts S a b).length = 1) (k : Nat) :
 OriginalWithin T S k ↔ ∃ c, c ∈ twoBranches S a b ∧
 ∃ r, remaining k c = some r ∧ ChildWithin T S c r := by
 constructor
 · intro h
   exact ⟨pendantChild S a b,by simp [twoBranches],(actual_t1_decision hnT hnS same hc one k).1 h⟩
 · rintro ⟨c,hm,hr⟩
   have hm3 : c ∈ branches S a b := by
     have hh : c = singletonChild S a ∨ c = pendantChild S a b := by simpa [twoBranches] using hm
     rcases hh with rfl | rfl <;> simp [branches]
   obtain ⟨hp,he,paid⟩ := branch_checks hnT hnS same hc hm3
   obtain ⟨F,hF,hk⟩ := (remaining_correct k hp he paid).2 hr
   exact ⟨F,hF.1,hk⟩

/-- Actual executable child calls: refusals are represented by remaining=None;
the child receives its literal source forest, permanent partition, and budget. -/
def childCall (solver : Child → Nat → Option (List (List Nat))) (k : Nat) (c : Child) :=
 (remaining k c).bind fun r => solver c r

def ExactBoundedChild (T S : Tree) (solver : Child → Nat → Option (List (List Nat)))
 (c : Child) : Prop :=
 (∀ r, (∃ G, solver c r = some G) ↔ ChildWithin T S c r) ∧
 (∀ r G, solver c r = some G → ExactChild T S c G ∧ G.length-c.partition.length ≤ r)

theorem child_call_success {T S : Tree} {solver : Child → Nat → Option (List (List Nat))}
 {c : Child} (ih : ExactBoundedChild T S solver c) (k : Nat) :
 (∃ G, childCall solver k c = some G) ↔
 ∃ r, remaining k c = some r ∧ ChildWithin T S c r := by
 unfold childCall
 cases hr : remaining k c with
 | none => simp [hr]
 | some r => simpa using ih.1 r

theorem high_child_solver_iff {T S : Tree} {p : RMAF.Vertex} {a b : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (hc : CoreGraph.CherryAt T p a b) (high : 3 ≤ (cuts S a b).length)
 (solver : Child → Nat → Option (List (List Nat)))
 (ih : ∀ c, c ∈ branches S a b → ExactBoundedChild T S solver c) (k : Nat) :
 OriginalWithin T S k ↔ ∃ c, c ∈ branches S a b ∧ ∃ G, childCall solver k c = some G := by
 rw [actual_high_budget hnT hnS same hc high k]
 constructor
 · rintro ⟨c,hm,hr⟩; exact ⟨c,hm,(child_call_success (ih c hm) k).2 hr⟩
 · rintro ⟨c,hm,hG⟩; exact ⟨c,hm,(child_call_success (ih c hm) k).1 hG⟩

theorem t1_child_solver_iff {T S : Tree} {p : RMAF.Vertex} {a b : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (hc : CoreGraph.CherryAt T p a b) (one : (cuts S a b).length = 1)
 (solver : Child → Nat → Option (List (List Nat)))
 (ih : ∀ c, c ∈ twoBranches S a b → ExactBoundedChild T S solver c) (k : Nat) :
 OriginalWithin T S k ↔ ∃ c, c ∈ twoBranches S a b ∧ ∃ G, childCall solver k c = some G := by
 rw [actual_t1_two_budget hnT hnS same hc one k]
 constructor
 · rintro ⟨c,hm,hr⟩; exact ⟨c,hm,(child_call_success (ih c hm) k).2 hr⟩
 · rintro ⟨c,hm,hG⟩; exact ⟨c,hm,(child_call_success (ih c hm) k).1 hG⟩
end Universal233.CherryBranching
