import T1Exchange
namespace Universal233.CherryBranching
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent

def twoBranches (S : Tree) (a b : Nat) : List Child :=
 [singletonChild S a,pendantChild S a b]

/-- Strong no-larger original agreement exchange used by the deterministic
t1 rule. The theorem below constructs it from the original graph hypotheses. -/
def T1PendantExchange (T S : Tree) (a b : Nat) : Prop :=
 ∀ F, agreement T S F = true → ∃ G, agreement T S G = true ∧
 G.length ≤ F.length ∧ Refines G (pendantPartition S a b)

/-- The originally pinned graph target, now discharged below. -/
def T1Target : Prop :=
 ∀ T S p a b, (leaves T).Nodup → (leaves S).Nodup →
 (∀ x, x ∈ leaves T ↔ x ∈ leaves S) → CherryAt T p a b →
 (cuts S a b).length = 1 → T1PendantExchange T S a b

/-- Two-branch consumer under a named exchange contract. The unconditional
source theorem below proves that contract under the actual t1 hypotheses. -/
theorem conditional_two_minimum {T S : Tree} {a b : Nat}
 (exchange : T1PendantExchange T S a b)
 (solve : Child → List (List Nat))
 (ih : ∀ c, c ∈ twoBranches S a b → ExactChild T S c (solve c))
 (best : List (List Nat))
 (chosen : ∃ c, c ∈ twoBranches S a b ∧ best = solve c)
 (least : ∀ c, c ∈ twoBranches S a b → best.length ≤ (solve c).length) :
 agreement T S best = true ∧ ∀ F, agreement T S F = true → best.length ≤ F.length := by
 obtain ⟨c,hc,rfl⟩ := chosen
 refine ⟨(ih c hc).1.1,?_⟩
 intro F hF
 obtain ⟨G,hG,hlen,href⟩ := exchange F hF
 have hm : pendantChild S a b ∈ twoBranches S a b := by simp [twoBranches]
 have hf : feasible T S (pendantChild S a b) G := ⟨hG,href⟩
 exact Nat.le_trans (least _ hm) (Nat.le_trans ((ih _ hm).2 G hf) hlen)

/-- Useful corrected route: actual ORIGINAL t1 agreements are covered by all
three literal branches without any exchange hypothesis. It retains paid cost1
on each branch, and supplies no improved t1 recurrence. -/
theorem unconditional_t1_three_cover {T S : Tree} {F : List (List Nat)}
 (hn : (leaves S).Nodup) (ha : agreement T S F = true)
 {p : RMAF.Vertex} {a b : Nat} (hc : CherryAt T p a b)
 (_one : (cuts S a b).length = 1) :
 ∃ c, c ∈ branches S a b ∧ feasible T S c F := ordinary_branches_cover hn ha hc
theorem actual_t1_target : T1Target := by
 intro T S p a b hnT hnS same hc one F hF
 exact actual_t1_pendant_exchange hnT hnS same hF hc one

/-- Requested safe t1 two-branch minimum, with actual original hypotheses and
child-specific exact solver IH. Both children have literal paid cost one. -/
theorem actual_t1_two_minimum {T S : Tree} {p : RMAF.Vertex} {a b : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (hc : CoreGraph.CherryAt T p a b) (one : (cuts S a b).length = 1)
 (solve : Child → List (List Nat))
 (ih : ∀ c, c ∈ twoBranches S a b → ExactChild T S c (solve c))
 (best : List (List Nat))
 (chosen : ∃ c, c ∈ twoBranches S a b ∧ best = solve c)
 (least : ∀ c, c ∈ twoBranches S a b → best.length ≤ (solve c).length) :
 agreement T S best = true ∧ ∀ F, agreement T S F = true → best.length ≤ F.length := by
 apply conditional_two_minimum (solve:=solve) (best:=best) _ ih chosen least
 intro F hF
 exact actual_t1_pendant_exchange hnT hnS same hF hc one

/-- The retained baseline actually permits the deterministic pendant child.
This theorem still assumes an exact solver for this SPECIFIC literal child. -/
theorem actual_t1_deterministic_minimum {T S : Tree} {p : RMAF.Vertex} {a b : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (hc : CoreGraph.CherryAt T p a b) (one : (cuts S a b).length = 1)
 {G : List (List Nat)} (ih : ExactChild T S (pendantChild S a b) G) :
 agreement T S G = true ∧ ∀ F, agreement T S F = true → G.length ≤ F.length := by
 refine ⟨ih.1.1,?_⟩
 intro F hF
 obtain ⟨H,hH,hlen,href⟩ := actual_t1_pendant_exchange hnT hnS same hF hc one
 exact Nat.le_trans (ih.2 H ⟨hH,href⟩) hlen
end Universal233.CherryBranching
