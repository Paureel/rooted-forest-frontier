import ForestProgram
namespace ForestMinCompletion
open RMAF GenericForest

/-- Exactly the soundness/completeness semantics of OrdinaryIH, restricted
only by the actual callback query budget. Properness remains its original
guard; no hypothesis constrains an improper callback's result. -/
structure LocalOrdinaryIH (K : Nat) (actual : Tree → Tree → Nat → Option Forest) where
 sound : ∀ t s b F, b ≤ K → Universal233.DepthOne.proper t s = true → actual t s b = some F →
   agreement t s F = true ∧ F.length-1 ≤ b ∧
     ∀ G, agreement t s G = true → F.length ≤ G.length
 complete : ∀ t s b G, b ≤ K → Universal233.DepthOne.proper t s = true → agreement t s G = true →
   G.length-1 ≤ b → ∃ F, actual t s b = some F

/-- Nat well-order, proved from strong induction and one actual witness. -/
theorem nat_minimum_from_witness (P : Nat → Prop) (n : Nat) :
 P n → ∃ m, P m ∧ ∀ k, P k → m ≤ k := by
 classical
 induction n using Nat.strongRecOn with
 | ind n ih =>
   intro pn
   by_cases smaller : ∃ m, m < n ∧ P m
   · obtain ⟨m,mn,pm⟩ := smaller
     exact ih m mn pm
   · refine ⟨n,pn,?_⟩
     intro k pk
     have no : ¬k < n := fun kn => smaller ⟨k,kn,pk⟩
     omega

/-- A desired minimum is derived from an actual original agreement forest.
Neither an ordinary solver nor its IH is used. The pairs may be improper. -/
theorem minimum_from_original_AF {t s : Tree} {F : Forest} (ha : agreement t s F = true) :
 ∃ M, agreement t s M = true ∧ ∀ G, agreement t s G = true → M.length ≤ G.length := by
 obtain ⟨m,⟨M,hM,len⟩,least⟩ := nat_minimum_from_witness
   (fun n => ∃ G : Forest, agreement t s G = true ∧ G.length = n) F.length ⟨F,ha,rfl⟩
 refine ⟨M,hM,?_⟩
 intro G hG
 rw [len]
 exact least G.length ⟨G,hG,rfl⟩

theorem minimum_feasible_from_original_AF {t s : Tree} {b : Nat}
 (feasible : ∃ F : Forest, agreement t s F = true ∧ F.length-1 ≤ b) :
 ∃ M, agreement t s M = true ∧ M.length-1 ≤ b ∧
   ∀ G, agreement t s G = true → M.length ≤ G.length := by
 obtain ⟨F,hF,budget⟩ := feasible
 obtain ⟨M,hM,least⟩ := minimum_from_original_AF hF
 exact ⟨M,hM,Nat.le_trans (Nat.sub_le_sub_right (least F hF) 1) budget,least⟩

/-- Mathematical choice only. This noncomputable value has no executable
callback implementation or runtime interpretation. All uses below are proofs. -/
noncomputable def minimumCallback (t s : Tree) (b : Nat) : Option Forest := by
 classical
 exact if h : ∃ F : Forest, agreement t s F = true ∧ F.length-1 ≤ b
   then some (Classical.choose (minimum_feasible_from_original_AF h)) else none

theorem minimumCallback_sound {t s : Tree} {b : Nat} {F : Forest}
 (answer : minimumCallback t s b = some F) :
 agreement t s F = true ∧ F.length-1 ≤ b ∧
   ∀ G, agreement t s G = true → F.length ≤ G.length := by
 classical
 unfold minimumCallback at answer
 split at answer
 · rename_i feasible
   have eq := Option.some.inj answer
   rw [←eq]
   exact Classical.choose_spec (minimum_feasible_from_original_AF feasible)
 · contradiction

theorem minimumCallback_complete {t s : Tree} {b : Nat} {G : Forest}
 (ha : agreement t s G = true) (budget : G.length-1 ≤ b) :
 ∃ F, minimumCallback t s b = some F := by
 classical
 have feasible : ∃ F : Forest, agreement t s F = true ∧ F.length-1 ≤ b := ⟨G,ha,budget⟩
 unfold minimumCallback
 rw [dite_eq_left feasible]
 exact ⟨_,rfl⟩

theorem minimumCallback_none_iff (t s : Tree) (b : Nat) :
 minimumCallback t s b = none ↔ ¬∃ F : Forest, agreement t s F = true ∧ F.length-1 ≤ b := by
 classical
 constructor
 · intro answer feasible
   obtain ⟨G,hG,budget⟩ := feasible
   obtain ⟨F,hF⟩ := minimumCallback_complete hG budget
   rw [answer] at hF
   contradiction
 · intro absent
   simp [minimumCallback,absent]

/-- Erased mathematical support for bounded-callback arguments. The actual
callback is retained on ALL low-budget pairs, even improper pairs. Beyond K
the proof-only choice is a feasible original-AF minimum or none. -/
noncomputable def ghost (K : Nat) (actual : Tree → Tree → Nat → Option Forest)
 (t s : Tree) (b : Nat) : Option Forest :=
 if b ≤ K then actual t s b else minimumCallback t s b

theorem ghost_eq_actual (K : Nat) (actual : Tree → Tree → Nat → Option Forest)
 (t s : Tree) (b : Nat) (low : b ≤ K) : ghost K actual t s b = actual t s b := by
 simp [ghost,low]

theorem ghost_above_budget (K : Nat) (actual : Tree → Tree → Nat → Option Forest)
 (t s : Tree) (b : Nat) (high : K < b) : ghost K actual t s b = minimumCallback t s b := by
 have no : ¬b ≤ K := by omega
 simp [ghost,no]

theorem ghost_global_ordinaryIH {K : Nat} {actual : Tree → Tree → Nat → Option Forest}
 (localIH : LocalOrdinaryIH K actual) : OrdinaryIH (ghost K actual) := by
 refine ⟨?_,?_⟩
 · intro t s b F proper answer
   by_cases low : b ≤ K
   · exact localIH.sound t s b F low proper (by simpa [ghost,low] using answer)
   · exact minimumCallback_sound (by simpa [ghost,low] using answer)
 · intro t s b G proper hG budget
   by_cases low : b ≤ K
   · obtain ⟨F,hF⟩ := localIH.complete t s b G low proper hG budget
     exact ⟨F,by simpa [ghost,low] using hF⟩
   · obtain ⟨F,hF⟩ := minimumCallback_complete hG budget
     exact ⟨F,by simpa [ghost,low] using hF⟩

/-- The totalized object is existential proof support, not a replacement
program. Only the supplied actual callback runs in a bounded caller. -/
theorem ordinaryIH_extension {K : Nat} {actual : Tree → Tree → Nat → Option Forest}
 (localIH : LocalOrdinaryIH K actual) :
 ∃ completed : Tree → Tree → Nat → Option Forest, OrdinaryIH completed ∧
   ∀ t s b, b ≤ K → completed t s b = actual t s b := by
 exact ⟨ghost K actual,ghost_global_ordinaryIH localIH,ghost_eq_actual K actual⟩

end ForestMinCompletion
