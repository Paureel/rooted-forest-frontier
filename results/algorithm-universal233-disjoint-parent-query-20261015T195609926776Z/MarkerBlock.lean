import HeadPermutation
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge

theorem stable_back_marker_not_singleton (T S t s mt ms : Tree) (X : List Nat) (y rho m : Nat)
    (ht : restrict X T=some t) (hs : restrict X S=some s)
    (hmt : marked T X y rho=some mt) (hms : marked S X y rho=some ms)
    (hn : y∉X) (hm : IsMinimum t s m)
    (F : List (List Nat)) (ha : agreement mt ms F=true) (hc : F.length-1=m) :
    [y]∉relabelForest (swap y rho) F := by
  intro hsingle
  have hdel := marked_deletion_spec T S t s mt ms X y rho ht hs hmt hms F ha
  have hlen : (clip X (relabelForest (swap y rho) F)).length<
      (relabelForest (swap y rho) F).length :=
    List.length_filterMap_lt_length_iff_exists.2 ⟨[y],hsingle,by simp [clipBlock,hn]⟩
  have low := hm.2 _ hdel.1
  have ne := Universal233.DepthOne.agreement_nonempty t s _ hdel.1
  have pos := List.length_pos_iff.2 ne
  rw [relabelForest_length] at hlen
  omega

/-- Select the actual marker-owning block from an arbitrary literal family,
retaining its outer permutation and inner label permutation separately. -/
theorem checked_marker_block (X : List Nat) (y : Nat) (G : List (List Nat))
    (hp : partitionCheck (y::X) G=true) (hn : y∉X) (ns : [y]∉G) :
    ∃ H K FX, G.Perm (H::FX) ∧ H.Perm (K++[y]) ∧ K≠[] ∧ K⊆X ∧
      (∀E∈FX,E⊆X) ∧ G.length=(K::FX).length := by
  obtain ⟨H,hH,hyH⟩ := checked_covers (y::X) G hp (by simp : y∈y::X)
  let FX := G.erase H
  let K := H.filter (X.contains ·)
  have outer : G.Perm (H::FX) := List.perm_cons_erase hH
  have phead := BinaryExchange.partition_perm (y::X) G (H::FX) outer hp
  have nH : H.Nodup := checked_block_nodup _ G hp H hH
  have neH : H≠[] := checked_nonempty _ G hp H hH
  have ksub : K⊆X := by intro x hx;exact List.contains_iff_mem.1 (List.mem_filter.1 hx).2
  have kempty : K≠[] := by
    intro he
    have subH : H⊆[y] := by
      intro x hx
      rcases List.mem_cons.1 (checked_label (y::X) G hp hH hx) with heq | hxX
      · simp [heq]
      · have memK : x∈K := List.mem_filter.2 ⟨hx,List.contains_iff_mem.2 hxX⟩
        rw [he] at memK
        contradiction
    have lit := ForestState.subset_singleton_eq H y neH subH nH
    exact ns (lit ▸ hH)
  have complement : H.filter (fun x => !(X.contains x))=[y] := by
    apply ForestState.subset_singleton_eq
    · intro he
      have hyf : y∈H.filter (fun x => !(X.contains x)) := by simp [hyH,hn]
      rw [he] at hyf
      contradiction
    · intro x hx
      have hxp := checked_label (y::X) G hp hH (List.mem_filter.1 hx).1
      rcases List.mem_cons.1 hxp with he | hxX
      · simp [he]
      · have htrue := (List.mem_filter.1 hx).2
        simp [hxX] at htrue
    · exact nH.filter _
  have inner : H.Perm (K++[y]) := by
    have h := List.filter_append_perm (X.contains ·) H
    rw [complement] at h
    exact h.symm
  have noYtail : y∉FX.flatten := by
    have count := checked_count (y::X) (H::FX) phead (by simp : y∈y::X)
    have pos : 0<H.count y := List.count_pos_iff.2 hyH
    simp only [List.flatten_cons,List.count_append] at count
    have zero : FX.flatten.count y=0 := by omega
    exact List.count_eq_zero.1 zero
  have fsub : ∀E∈FX,E⊆X := by
    intro E hE x hx
    have hxl := checked_label (y::X) (H::FX) phead (List.mem_cons_of_mem H hE) hx
    rcases List.mem_cons.1 hxl with he | hxX
    · subst x
      exact False.elim (noYtail (List.mem_flatten.2 ⟨E,hE,hx⟩))
    · exact hxX
  exact ⟨H,K,FX,outer,inner,kempty,ksub,fsub,by simpa using outer.length_eq⟩
end OrdinaryCommonSplit
