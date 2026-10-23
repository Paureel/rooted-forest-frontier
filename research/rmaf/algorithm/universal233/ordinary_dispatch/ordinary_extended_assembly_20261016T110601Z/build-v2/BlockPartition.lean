import CommonCherryContraction

namespace ForestState
open RMAF RestrictionBridge

def Coalesced (F : List (List Nat)) (a b : Nat) := ∀ B ∈ F, a ∈ B ↔ b ∈ B

theorem together_coalesced (L : List Nat) (F : List (List Nat)) (a b : Nat)
    (hp : partitionCheck L F = true) (A : List Nat) (hA : A ∈ F) (ha : a ∈ A) (hb : b ∈ A) :
    Coalesced F a b := by
  intro B hB
  constructor
  · intro hm
    have he := checked_unique_block L F hp B A hB hA a hm ha
    simpa [he] using hb
  · intro hm
    have he := checked_unique_block L F hp B A hB hA b hm hb
    simpa [he] using ha

theorem nodup_count_one (B : List Nat) (nd : B.Nodup) (x : Nat) (hx : x ∈ B) : B.count x = 1 := by
  have hp := List.count_pos_iff.2 hx
  have hq := List.nodup_iff_count.1 nd x
  omega

theorem count_filter_exact (B : List Nat) (p : Nat → Bool) (x : Nat) :
    (B.filter p).count x = if p x then B.count x else 0 := by
  induction B with
  | nil => simp
  | cons y B ih =>
    by_cases he : y = x
    · subst y
      cases hp : p x <;> simp [hp,ih]
    · cases hp : p y <;> simp [hp,he,ih]

theorem contractBlock_count (B : List Nat) (a b z x : Nat) (nd : B.Nodup)
    (hz : z ∉ B) (sat : a ∈ B ↔ b ∈ B) :
    (contractBlock a b z B).count x =
      if x = z then B.count a else if x = a ∨ x = b then 0 else B.count x := by
  by_cases ha : a ∈ B
  · have hb := sat.mp ha
    have hca := nodup_count_one B nd a ha
    have hcz := List.count_eq_zero.2 hz
    have hza : z ≠ a := by intro he; subst z; exact hz ha
    have hzb : z ≠ b := by intro he; subst z; exact hz hb
    by_cases hxz : x = z <;> by_cases hxa : x = a <;> by_cases hxb : x = b <;>
      simp_all [contractBlock,count_filter_exact,List.count_cons] <;> simp_all [eq_comm]
  · have hb : b ∉ B := fun hm => ha (sat.mpr hm)
    have hca := List.count_eq_zero.2 ha
    have hcb := List.count_eq_zero.2 hb
    have hcz := List.count_eq_zero.2 hz
    by_cases hxz : x = z <;> by_cases hxa : x = a <;> by_cases hxb : x = b <;>
      simp_all [contractBlock] <;> simp_all [eq_comm]

theorem contracted_forest_count (F : List (List Nat)) (a b z x : Nat)
    (nd : ∀ B ∈ F, B.Nodup) (hz : ∀ B ∈ F, z ∉ B) (sat : Coalesced F a b) :
    ((F.map (contractBlock a b z)).flatten).count x =
      if x = z then F.flatten.count a else if x = a ∨ x = b then 0 else F.flatten.count x := by
  induction F with
  | nil => simp
  | cons B F ih =>
    have hi := ih (fun C hC => nd C (by simp [hC]))
      (fun C hC => hz C (by simp [hC])) (fun C hC => sat C (by simp [hC]))
    have hc := contractBlock_count B a b z x (nd B (by simp)) (hz B (by simp)) (sat B (by simp))
    simp only [List.map_cons,List.flatten_cons,List.count_append,hc,hi]
    by_cases hxz : x = z <;> by_cases hx : x = a ∨ x = b <;> simp [hxz,hx]

theorem partition_by_counts (L : List Nat) (F : List (List Nat)) (nd : L.Nodup)
    (ne : ∀ B ∈ F, B ≠ []) (counts : ∀ x, F.flatten.count x = L.count x) :
    partitionCheck L F = true := by
  simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro B hB; simpa using ne B hB
  · intro x hx
    apply beq_iff_eq.2
    rw [counts x,nodup_count_one L nd x hx]
  · intro x hx
    apply List.contains_iff_mem.2
    apply List.count_pos_iff.1
    rw [←counts x]
    exact List.count_pos_iff.2 hx

theorem partition_counts (L : List Nat) (F : List (List Nat)) (hp : partitionCheck L F = true)
    (nd : L.Nodup) (x : Nat) : F.flatten.count x = L.count x := by
  by_cases hx : x ∈ L
  · rw [checked_count L F hp hx,nodup_count_one L nd x hx]
  · have hf : x ∉ F.flatten := by
      intro hm
      obtain ⟨B,hB,hxB⟩ := List.mem_flatten.1 hm
      exact hx (checked_label L F hp hB hxB)
    rw [List.count_eq_zero.2 hf,List.count_eq_zero.2 hx]

theorem contraction_partition (t : Tree) (F : List (List Nat)) (a b z : Nat)
    (nd : (leaves t).Nodup) (ch : cherry a b t = true) (hz : z ∉ leaves t)
    (hp : partitionCheck (leaves t) F = true) (sat : Coalesced F a b) :
    partitionCheck (leaves (contract a b z t)) (F.map (contractBlock a b z)) = true := by
  obtain ⟨w,hw⟩ := cherry_at_exists t a b ch
  apply partition_by_counts _ _ (contraction_nodup t a b z nd ch hz)
  · intro D hD
    obtain ⟨B,hB,rfl⟩ := List.mem_map.1 hD
    have hn := checked_nonempty (leaves t) F hp B hB
    by_cases ha : a ∈ B
    · simp [contractBlock,ha]
    · simpa [contractBlock,ha] using hn
  · intro x
    rw [contracted_forest_count F a b z x
      (fun B hB => checked_block_nodup (leaves t) F hp B hB)
      (fun B hB hm => hz (checked_label (leaves t) F hp hB hm)) sat,
      hw.contract_count z x nd hz,checked_count (leaves t) F hp hw.labels.1]
    by_cases hxz : x = z <;> by_cases hx : x = a ∨ x = b <;>
      simp [hxz,hx,partition_counts (leaves t) F hp nd x]

theorem contraction_additional_cost (ss : List Tree) (F : List (List Nat)) (a b z : Nat) :
    additionalCost (ss.map (contract a b z)) (F.map (contractBlock a b z)) =
      additionalCost ss F := by simp [additionalCost]

theorem expansion_additional_cost (ss : List Tree) (F : List (List Nat)) (a b z : Nat) :
    additionalCost (ss.map (expand a b z)) (F.map (expandBlock a b z)) =
      additionalCost ss F := by simp [additionalCost]

end ForestState
