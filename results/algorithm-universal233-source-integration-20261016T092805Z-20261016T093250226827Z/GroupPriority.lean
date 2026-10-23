import GroupCostProof
namespace ForestGroups
open RMAF RestrictionBridge ForestState

@[simp] theorem owned_append (ss rs : List Tree) (U : List Nat) :
    owned (ss ++ rs) U = owned ss U ++ owned rs U := by simp [owned,List.filter_append]

theorem owned_within (ss : List Tree) (U : List Nat) (h : ∀ s ∈ ss, leaves s ⊆ U) :
    owned ss U = ss := by
  apply List.filter_eq_self.2
  intro s hs
  exact (contained_iff _ _).2 (h s hs)

theorem owned_outside (L : List Nat) (Q : List (List Nat))
    (hq : partitionCheck L Q = true) (U V : List Nat) (hU : U ∈ Q) (hV : V ∈ Q)
    (hne : U ≠ V) (ss : List Tree) (h : ∀ s ∈ ss, leaves s ⊆ V) : owned ss U = [] := by
  apply List.filter_eq_nil_iff.2
  intro s hs hc
  exact hne (block_group_owner L Q hq U V (leaves s) hU hV (leaves_nonempty s)
    ((contained_iff _ _).1 hc) (h s hs))

theorem three_owned (T : Option Tree) (a : Tree) (bs cs : List Tree) (A B C : List Nat)
    (hq : partitionCheck (labels T) [A,B,C] = true)
    (ha : leaves a ⊆ A) (hb : ∀ s ∈ bs, leaves s ⊆ B) (hc : ∀ s ∈ cs, leaves s ⊆ C) :
    owned ([a] ++ bs ++ cs) A = [a] ∧ owned ([a] ++ bs ++ cs) B = bs ∧
      owned ([a] ++ bs ++ cs) C = cs := by
  have hab : A ≠ B := by
    intro eq; subst B
    have := checked_family_nodup _ _ hq
    simp at this
  have hac : A ≠ C := by
    intro eq; subst C
    have := checked_family_nodup _ _ hq
    simp at this
  have hbc : B ≠ C := by
    intro eq; subst C
    have := checked_family_nodup _ _ hq
    simp at this
  have hA : A ∈ [A,B,C] := by simp
  have hB : B ∈ [A,B,C] := by simp
  have hC : C ∈ [A,B,C] := by simp
  have hsa : ∀ s ∈ [a], leaves s ⊆ A := by simpa using ha
  simp only [owned_append]
  rw [owned_within [a] A hsa,
    owned_outside _ _ hq A B hA hB hab bs hb,
    owned_outside _ _ hq A C hA hC hac cs hc,
    owned_outside _ _ hq B A hB hA (Ne.symm hab) [a] hsa,
    owned_within bs B hb,
    owned_outside _ _ hq B C hB hC hbc cs hc,
    owned_outside _ _ hq C A hC hA (Ne.symm hac) [a] hsa,
    owned_outside _ _ hq C B hC hB (Ne.symm hbc) bs hb,
    owned_within cs C hc]
  simp

def PriorityClear (T : Option Tree) (a : Tree) (bs cs : List Tree) : Prop :=
  ∀ t, T = some t →
    (∀ b ∈ bs, Clear (minimalVertices (leaves a) t) (minimalVertices (leaves b) t)) ∧
    (∀ c ∈ cs, Clear (minimalVertices (leaves a) t) (minimalVertices (leaves c) t)) ∧
    (∀ b ∈ bs, ∀ c ∈ cs, Clear (minimalVertices (leaves b) t) (minimalVertices (leaves c) t))

theorem priority_cross (T : Option Tree) (a : Tree) (bs cs : List Tree) (A B C : List Nat)
    (eqs : owned ([a] ++ bs ++ cs) A = [a] ∧ owned ([a] ++ bs ++ cs) B = bs ∧
      owned ([a] ++ bs ++ cs) C = cs)
    (clear : PriorityClear T a bs cs) : CrossClear T ([a] ++ bs ++ cs) [A,B,C] := by
  intro t ht U hU V hV hne s hs r hr
  have hh := clear t ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hU hV
  rcases hU with rfl | rfl | rfl <;> rcases hV with rfl | rfl | rfl
  all_goals try exact False.elim (hne rfl)
  all_goals simp only [eqs.1,eqs.2.1,eqs.2.2,List.mem_singleton] at hs hr
  · subst s; exact hh.1 r hr
  · subst s; exact hh.2.1 r hr
  · subst r; exact (clear_symm _ _).1 (hh.1 s hs)
  · exact hh.2.2 s hs r hr
  · subst r; exact (clear_symm _ _).1 (hh.2.1 s hs)
  · exact (clear_symm _ _).1 (hh.2.2 r hr s hs)

/-- A literal cost-one A agreement combines with ANY residual B-forest agreement
and a completed C agreement. Target overlap between distinct B source pieces is
allowed. The paid one is an explicit agreement cost, not a minimum discount. -/
theorem retained_A_one_plus_Bforest (T : Option Tree) (a : Tree) (bs cs : List Tree)
    (A B C : List Nat) (FA FB FC : List (List Nat))
    (hp : proper T ([a] ++ bs ++ cs) = true)
    (hq : partitionCheck (labels T) [A,B,C] = true)
    (ownsA : leaves a ⊆ A) (ownsB : ∀ s ∈ bs, leaves s ⊆ B)
    (ownsC : ∀ s ∈ cs, leaves s ⊆ C) (clear : PriorityClear T a bs cs)
    (hA : agrees (localTarget T A) [a] FA = true) (costA : additionalCost [a] FA = 1)
    (hB : agrees (localTarget T B) bs FB = true)
    (hC : agrees (localTarget T C) cs FC = true) (costC : additionalCost cs FC = 0) :
    agrees T ([a] ++ bs ++ cs) (FA ++ FB ++ FC) = true ∧
    additionalCost ([a] ++ bs ++ cs) (FA ++ FB ++ FC) = 1 + additionalCost bs FB := by
  have eqs := three_owned T a bs cs A B C hq ownsA ownsB ownsC
  have own : Owns ([a] ++ bs ++ cs) [A,B,C] := by
    intro s hs
    simp only [List.mem_append,List.mem_singleton] at hs
    rcases hs with (rfl | hs) | hs
    · exact ⟨A,by simp,ownsA⟩
    · exact ⟨B,by simp,ownsB s hs⟩
    · exact ⟨C,by simp,ownsC s hs⟩
  have hab : A ≠ B := by intro eq; subst B; have := checked_family_nodup _ _ hq; simp at this
  have hac : A ≠ C := by intro eq; subst C; have := checked_family_nodup _ _ hq; simp at this
  have hbc : B ≠ C := by intro eq; subst C; have := checked_family_nodup _ _ hq; simp at this
  let G := fun U : List Nat => if U = A then FA else if U = B then FB else FC
  have gA : G A = FA := by simp [G]
  have gB : G B = FB := by simp [G,Ne.symm hab]
  have gC : G C = FC := by simp [G,Ne.symm hac,Ne.symm hbc]
  have hl : ∀ U ∈ [A,B,C], agrees (localTarget T U) (owned ([a] ++ bs ++ cs) U) (G U) = true := by
    intro U hU
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hU
    rcases hU with rfl | rfl | rfl
    · simpa only [eqs.1,gA] using hA
    · simpa only [eqs.2.1,gB] using hB
    · simpa only [eqs.2.2,gC] using hC
  have hr := reverse_reconstruction T ([a] ++ bs ++ cs) [A,B,C] G hp hq own
    (priority_cross T a bs cs A B C eqs clear) hl
  have hc := reverse_exact_cost T ([a] ++ bs ++ cs) [A,B,C] G hp hq own hl
  have hf : [A,B,C].flatMap G = FA ++ FB ++ FC := by simp [gA,gB,gC,List.append_assoc]
  rw [hf] at hr hc
  refine ⟨hr,?_⟩
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,eqs.1,eqs.2.1,eqs.2.2,gA,gB,gC,costA,costC] at hc
  omega

/-- Future recursive query contract. It concerns the whole current B FOREST.
This definition asserts no implementation, runtime, or solver theorem. -/
def ResidualSolverContract (solve : Option Tree → List Tree → Nat → Option (List (List Nat)))
    (TB : Option Tree) (bs : List Tree) (q : Nat) : Prop :=
  proper TB bs = true →
    ((solve TB bs q = none ↔ ∀ FB, agrees TB bs FB = true → q < additionalCost bs FB) ∧
     ∀ FB, solve TB bs q = some FB → agrees TB bs FB = true ∧ additionalCost bs FB ≤ q)

theorem paid_one_budget (a : Tree) (bs cs : List Tree) (FA FB FC : List (List Nat)) (q : Nat)
    (cost : additionalCost ([a] ++ bs ++ cs) (FA ++ FB ++ FC) = 1 + additionalCost bs FB)
    (positive : 0 < q) :
    additionalCost ([a] ++ bs ++ cs) (FA ++ FB ++ FC) ≤ q ↔ additionalCost bs FB ≤ q - 1 := by
  omega
end ForestGroups

namespace ForestGroups
open RMAF RestrictionBridge ForestState

/-- Conditional future q-1 query. The supplied contract must already be justified
for the restricted target and the WHOLE list bs of current B source trees. This
file supplies neither recursive termination nor an implementation of solve. -/
theorem residual_query_lift
    (solve : Option Tree → List Tree → Nat → Option (List (List Nat)))
    (T : Option Tree) (a : Tree) (bs cs : List Tree) (A B C : List Nat)
    (FA FB FC : List (List Nat)) (q : Nat) (positive : 0 < q)
    (IH : ResidualSolverContract solve (localTarget T B) bs (q-1))
    (hp : proper T ([a] ++ bs ++ cs) = true)
    (hq : partitionCheck (labels T) [A,B,C] = true)
    (ownsA : leaves a ⊆ A) (ownsB : ∀ s ∈ bs, leaves s ⊆ B)
    (ownsC : ∀ s ∈ cs, leaves s ⊆ C) (clear : PriorityClear T a bs cs)
    (hA : agrees (localTarget T A) [a] FA = true) (costA : additionalCost [a] FA = 1)
    (hC : agrees (localTarget T C) cs FC = true) (costC : additionalCost cs FC = 0)
    (query : solve (localTarget T B) bs (q-1) = some FB) :
    agrees T ([a] ++ bs ++ cs) (FA ++ FB ++ FC) = true ∧
    additionalCost ([a] ++ bs ++ cs) (FA ++ FB ++ FC) ≤ q := by
  have own : Owns ([a] ++ bs ++ cs) [A,B,C] := by
    intro s hs
    simp only [List.mem_append,List.mem_singleton] at hs
    rcases hs with (rfl | hs) | hs
    · exact ⟨A,by simp,ownsA⟩
    · exact ⟨B,by simp,ownsB s hs⟩
    · exact ⟨C,by simp,ownsC s hs⟩
  have eqB := (three_owned T a bs cs A B C hq ownsA ownsB ownsC).2.1
  have pB : proper (localTarget T B) bs = true := by
    simpa only [eqB] using local_proper T ([a] ++ bs ++ cs) [A,B,C] hp hq own B (by simp)
  obtain ⟨hB,budgetB⟩ := (IH pB).2 FB query
  obtain ⟨hag,cost⟩ := retained_A_one_plus_Bforest T a bs cs A B C FA FB FC
    hp hq ownsA ownsB ownsC clear hA costA hB hC costC
  exact ⟨hag,by omega⟩

theorem residual_query_complete
    (solve : Option Tree → List Tree → Nat → Option (List (List Nat)))
    (TB : Option Tree) (bs : List Tree) (q : Nat)
    (IH : ResidualSolverContract solve TB bs q)
    (hp : proper TB bs = true) (FB : List (List Nat))
    (ha : agrees TB bs FB = true) (cost : additionalCost bs FB ≤ q) :
    ∃ G, solve TB bs q = some G ∧ agrees TB bs G = true ∧ additionalCost bs G ≤ q := by
  cases hs : solve TB bs q with
  | none =>
    have impossible := (IH hp).1.1 hs FB ha
    omega
  | some G =>
    obtain ⟨hG,hcost⟩ := (IH hp).2 G hs
    exact ⟨G,rfl,hG,hcost⟩
end ForestGroups

namespace ForestGroups
open RMAF RestrictionBridge ForestState

/-- Empty completed-C boundary: use the actual two-group partition [A,B]. -/
theorem retained_A_one_Bforest_no_C (T : Option Tree) (a : Tree) (bs : List Tree)
    (A B : List Nat) (FA FB : List (List Nat))
    (hp : proper T ([a] ++ bs) = true) (hq : partitionCheck (labels T) [A,B] = true)
    (ownsA : leaves a ⊆ A) (ownsB : ∀ s ∈ bs, leaves s ⊆ B)
    (clear : ∀ t, T = some t → ∀ b ∈ bs,
      Clear (minimalVertices (leaves a) t) (minimalVertices (leaves b) t))
    (hA : agrees (localTarget T A) [a] FA = true) (costA : additionalCost [a] FA = 1)
    (hB : agrees (localTarget T B) bs FB = true) :
    agrees T ([a] ++ bs) (FA ++ FB) = true ∧
      additionalCost ([a] ++ bs) (FA ++ FB) = 1 + additionalCost bs FB := by
  have hab : A ≠ B := by intro eq; subst B; have := checked_family_nodup _ _ hq; simp at this
  have hAq : A ∈ [A,B] := by simp
  have hBq : B ∈ [A,B] := by simp
  have hsa : ∀ s ∈ [a], leaves s ⊆ A := by simpa using ownsA
  have eqA : owned ([a] ++ bs) A = [a] := by
    rw [owned_append,owned_within [a] A hsa,owned_outside _ _ hq A B hAq hBq hab bs ownsB,List.append_nil]
  have eqB : owned ([a] ++ bs) B = bs := by
    rw [owned_append,owned_outside _ _ hq B A hBq hAq (Ne.symm hab) [a] hsa,owned_within bs B ownsB,List.nil_append]
  have own : Owns ([a] ++ bs) [A,B] := by
    intro s hs
    simp only [List.mem_append,List.mem_singleton] at hs
    rcases hs with rfl | hs
    · exact ⟨A,hAq,ownsA⟩
    · exact ⟨B,hBq,ownsB s hs⟩
  let G := fun U : List Nat => if U = A then FA else FB
  have gA : G A = FA := by simp [G]
  have gB : G B = FB := by simp [G,Ne.symm hab]
  have hl : ∀ U ∈ [A,B], agrees (localTarget T U) (owned ([a] ++ bs) U) (G U) = true := by
    intro U hU
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hU
    rcases hU with rfl | rfl
    · simpa only [eqA,gA] using hA
    · simpa only [eqB,gB] using hB
  have cross : CrossClear T ([a] ++ bs) [A,B] := by
    intro t ht U hU V hV hne s hs r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hU hV
    rcases hU with rfl | rfl <;> rcases hV with rfl | rfl
    all_goals try exact False.elim (hne rfl)
    all_goals simp only [eqA,eqB,List.mem_singleton] at hs hr
    · subst s; exact clear t ht r hr
    · subst r; exact (clear_symm _ _).1 (clear t ht s hs)
  have hr := reverse_reconstruction T ([a] ++ bs) [A,B] G hp hq own cross hl
  have hc := reverse_exact_cost T ([a] ++ bs) [A,B] G hp hq own hl
  have hf : [A,B].flatMap G = FA ++ FB := by simp [gA,gB]
  rw [hf] at hr hc
  refine ⟨hr,?_⟩
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,eqA,eqB,gA,gB,costA] at hc
  omega
end ForestGroups
