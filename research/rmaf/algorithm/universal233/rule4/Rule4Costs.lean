import Rule4Selector

namespace Universal233.Rule4
open RMAF VertexGeometry CoreGraph Integration HardParent BinaryExchange CutRealization

theorem hasCherry_distinct {T : Tree} {a b : Nat} (hc : HasCherry a b T)
    (hn : (leaves T).Nodup) : a ≠ b := by
  induction hc with
  | here => simpa [leaves] using hn
  | swap =>
    have hh : b ≠ a := by simpa [leaves] using hn
    exact Ne.symm hh
  | left h ih => exact ih (List.nodup_append.1 hn).1
  | right h ih => exact ih (List.nodup_append.1 hn).2.1

theorem selected_swapped_cost (T S : Tree) (s : Choice T S) :
    2 ≤ (pendantOriginal T s.raw.a s.raw.c).length := by
  let a := s.raw.a
  let b := s.raw.b
  let c := s.raw.c
  have hcT := orderedCherries_sound s.admission.1
  have hcS := orderedCherries_sound s.admission.2.1
  have hab : a ≠ b := s.admission.2.2.1
  have hac : a ≠ c := hasCherry_distinct hcS s.priority.2.1
  have hblS : b ∈ leaves S := s.priority.2.2.1.mem_iff.1 (hasCherry_labels hcT).2
  have hclT : c ∈ leaves T := s.priority.2.2.1.mem_iff.2 (hasCherry_labels hcS).2
  have hq := two_cut_mem_left s.admission.2.2.2.1
  have hbc : b ≠ c := by
    have ho := source_label_outside_pendant hq (Or.inr rfl) hblS
    have he := s.admission.2.2.2.2
    simpa [he] using ho
  have positive : ∃ q, q ∈ pendantOriginal T a c := by
    have make (p : RMAF.Vertex) (sa sb : Bool)
        (hla : LeafAt T (p ++ [sa]) a) (hlb : LeafAt T (p ++ [sb]) b) :
        p ++ [sb] ∈ pendantOriginal T a c := by
      have hp := leaf_parent_hull hla [a,c] (by simp) ⟨c,by simp,hclT,Ne.symm hac⟩
      have hout : p ++ [sb] ∉ minimalVertices [a,c] T := by
        intro hm
        have hh := (minimalVertices_terminal [a,c] T _ b hlb).1 hm
        simp [Ne.symm hab,hbc] at hh
      apply (pendantOriginal_spec T a c (p ++ [sb])).2
      refine ⟨hlb.valid,by simp,?_,hout⟩
      simpa using hp
    obtain ⟨p,hp | hp⟩ := hasCherry_address hcT
    · exact ⟨p ++ [true],make p false true (cherry_left hp) (cherry_right hp)⟩
    · exact ⟨p ++ [false],make p true false (cherry_right hp) (cherry_left hp)⟩
  have hpos : 0 < (pendantOriginal T a c).length := by
    obtain ⟨q,hq⟩ := positive
    exact List.length_pos_of_mem hq
  have hnotone : (pendantOriginal T a c).length ≠ 1 := by
    have h := (List.all_eq_true.1 s.priority.2.2.2.2.2) (a,c) s.admission.2.1
    simpa only [bne_iff_ne] using h
  change 2 ≤ (pendantOriginal T a c).length
  omega

def costs (T S : Tree) (s : Choice T S) : List Nat :=
  [2,1,(pendantOriginal T s.raw.a s.raw.c).length]

theorem costs_positive {T S : Tree} (s : Choice T S) : ∀ d, d ∈ costs T S s → 0 < d := by
  intro d hd
  have hm := selected_swapped_cost T S s
  simp only [costs,List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl | rfl | rfl <;> omega

theorem callback_strict_decrease {T S : Tree} (s : Choice T S) (q d : Nat)
    (hd : d ∈ costs T S s) (hq : d ≤ q) : q - d < q := by
  have hp := costs_positive s d hd
  omega

theorem negpow_step (c : Rat) (hc : c ≠ 0) (n : Nat) :
    c ^ (-((n+1 : Nat) : Int)) = c ^ (-(n : Int)) * c⁻¹ := by
  have he : -((n+1 : Nat) : Int) = -(n : Int) + (-1 : Int) := by omega
  have hone : c ^ (-1 : Int) = c⁻¹ := by rw [Rat.zpow_neg c 1,Rat.zpow_one]
  rw [he,Rat.zpow_add hc,hone]

theorem negpow_mono (c : Rat) (hc : 2 ≤ c) (m : Nat) (hm : 2 ≤ m) :
    c ^ (-(m : Int)) ≤ c ^ (-2 : Int) := by
  have hcp : 0 < c := by grind
  have hcn : c ≠ 0 := Rat.ne_of_gt hcp
  have hinv : c⁻¹ ≤ 1 := by
    apply Rat.le_of_mul_le_mul_right (c := c) _ hcp
    rw [Rat.inv_mul_cancel c hcn,Rat.one_mul]
    grind
  induction hm with
  | refl => exact Rat.le_refl
  | @step m hm ih =>
    rw [negpow_step c hcn m]
    have hnp : 0 ≤ c ^ (-(m : Int)) := Rat.le_of_lt (Rat.zpow_pos hcp)
    have hs := Rat.mul_le_mul_of_nonneg_left hinv hnp
    rw [Rat.mul_one] at hs
    exact Rat.le_trans hs ih

def callbackMass (c : Rat) (q : Nat) (ds : List Nat) : Rat :=
  ((ds.filter (fun d => d ≤ q)).map (fun d : Nat => c ^ (-(d : Int)))).sum

theorem callback_mass_pruned (c : Rat) (hc : 2 ≤ c) (q : Nat) (ds : List Nat) :
    callbackMass c q ds ≤ (ds.map (fun d : Nat => c ^ (-(d : Int)))).sum := by
  induction ds with
  | nil => simp [callbackMass]
  | cons d ds ih =>
    have hp : 0 ≤ c ^ (-(d : Int)) := Rat.le_of_lt (Rat.zpow_pos (by grind : 0 < c))
    by_cases hd : d ≤ q
    · simp [callbackMass,hd] at ih ⊢ <;> grind
    · simp [callbackMass,hd] at ih ⊢ <;> grind

/-- Exact normalized callback LIST mass, with every budget-pruned callback
charged by its actual original cut count. This does not pay a local toll. -/
theorem selected_callback_mass {T S : Tree} (s : Choice T S)
    (c : Rat) (hc : 2 ≤ c) (q : Nat) :
    callbackMass c q (costs T S s) ≤ c ^ (-1 : Int) + 2 * c ^ (-2 : Int) := by
  have hp := callback_mass_pruned c hc q (costs T S s)
  have hm := negpow_mono c hc (pendantOriginal T s.raw.a s.raw.c).length
    (selected_swapped_cost T S s)
  simp only [costs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Rat.add_zero] at hp
  have algebra : ∀ x y z : Rat, z ≤ x → x + (y + z) ≤ y + 2*x := by
    intro x y z hz
    grind
  have hbound := algebra (c ^ (-2 : Int)) (c ^ (-1 : Int))
    (c ^ (-((pendantOriginal T s.raw.a s.raw.c).length : Int))) hm
  exact Rat.le_trans hp hbound
end Universal233.Rule4
