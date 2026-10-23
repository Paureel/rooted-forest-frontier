import Equivalence
namespace OutputState
open RMAF RestrictionBridge ForestState ForestGroups

theorem partition_permutation (L : List Nat) (F G : List (List Nat)) (p : F.Perm G) :
    partitionCheck L F = partitionCheck L G := by
  simp only [partitionCheck]
  have hc : (fun x => F.flatten.count x == 1) = (fun x => G.flatten.count x == 1) := by
    funext x; rw [p.flatten.count_eq x]
  rw [p.all_eq,hc,p.flatten.all_eq]

theorem source_permutation (T : Option Tree) (ss rs : List Tree)
    (p : ss.Perm rs) (F : List (List Nat)) :
    agrees T ss F = agrees T rs F := by
  have hp : proper T ss = proper T rs := by
    simp only [proper,partition_permutation _ _ _ (p.map leaves)]
  have hc : F.all (fun B => ss.any (fun s => contained B (leaves s))) =
      F.all (fun B => rs.any (fun s => contained B (leaves s))) := by
    congr 1
    funext B
    exact p.any_eq
  simp only [agrees,hp,hc,p.all_eq]

theorem cost_permutation (ss rs : List Tree) (p : ss.Perm rs) (F : List (List Nat)) :
    additionalCost ss F = additionalCost rs F := by simp only [additionalCost,p.length_eq]

theorem owned_three_permutation (T : Option Tree) (ss : List Tree) (A B C : List Nat)
    (hq : partitionCheck (labels T) [A,B,C] = true) (own : Owns ss [A,B,C]) :
    ss.Perm (owned ss A ++ owned ss B ++ owned ss C) := by
  have hab : A ≠ B := by intro eq; subst B; have := checked_family_nodup _ _ hq; simp at this
  have hac : A ≠ C := by intro eq; subst C; have := checked_family_nodup _ _ hq; simp at this
  have hbc : B ≠ C := by intro eq; subst C; have := checked_family_nodup _ _ hq; simp at this
  apply List.perm_iff_count.2
  intro s
  induction ss with
  | nil => simp [owned]
  | cons r ss ih =>
    have hs : Owns ss [A,B,C] := fun z hz => own z (by simp [hz])
    have hi := ih hs
    have ho := own r (by simp)
    obtain ⟨U,hU,hsub⟩ := ho
    have uniqueness : ∀ V ∈ [A,B,C], U ≠ V → ¬ leaves r ⊆ V := by
      intro V hV hne hv
      exact hne (block_group_owner _ _ hq U V (leaves r) hU hV (leaves_nonempty r) hsub hv)
    have hUtrue := (contained_iff (leaves r) U).2 hsub
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hU
    rcases hU with rfl | rfl | rfl
    · have hb : contained (leaves r) B = false := by
        cases h : contained (leaves r) B <;> simp_all [contained_iff]
      have hc : contained (leaves r) C = false := by
        cases h : contained (leaves r) C <;> simp_all [contained_iff]
      simp [owned,hUtrue,hb,hc,List.count_cons] at hi ⊢
      omega
    · have ha : contained (leaves r) A = false := by
        cases h : contained (leaves r) A <;> simp_all [contained_iff]
      have hc : contained (leaves r) C = false := by
        cases h : contained (leaves r) C <;> simp_all [contained_iff]
      simp [owned,hUtrue,ha,hc,List.count_cons] at hi ⊢
      omega
    · have ha : contained (leaves r) A = false := by
        cases h : contained (leaves r) A <;> simp_all [contained_iff]
      have hb : contained (leaves r) B = false := by
        cases h : contained (leaves r) B <;> simp_all [contained_iff]
      simp [owned,hUtrue,ha,hb,List.count_cons] at hi ⊢
      omega
end OutputState
