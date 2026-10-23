import Port
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge Universal233.CoreGraph

theorem Port.clip_labels_sub (c : Port) (U : List Nat) : (c.clip U).labels⊆c.labels := by
  induction c with
  | hole => simp [Port.clip,Port.labels]
  | left c r ih =>
    cases hr : restrict U r with
    | none =>
      simp only [Port.clip,hr,Port.labels]
      exact List.Subset.trans ih (by intro x hx;exact List.mem_append_left _ hx)
    | some v =>
      simp only [Port.clip,hr,Port.labels]
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact List.mem_append_left _ (ih hx)
      · exact List.mem_append_right _ ((restricted_labels_exact r v U hr).1 hx).1
  | right l c ih =>
    cases hl : restrict U l with
    | none =>
      simp only [Port.clip,hl,Port.labels]
      exact List.Subset.trans ih (by intro x hx;exact List.mem_append_right _ hx)
    | some v =>
      simp only [Port.clip,hl,Port.labels]
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact List.mem_append_left _ ((restricted_labels_exact l v U hl).1 hx).1
      · exact List.mem_append_right _ (ih hx)

theorem Port.restrict_join (c : Port) (u v : Tree) (K L : List Nat)
    (hK : ∀ x∈leaves u, x∉K) (hL : ∀ x∈c.labels, x∉L)
    (hu : restrict L u=some v) :
    restrict (K++L) (c.plug u)=some ((c.clip K).plug v) := by
  have hr : restrict (K++L) u=restrict L u := BinaryExchange.restrict_congr u _ _
    (by intro x hx;simp only [List.mem_append];exact ⟨fun h => h.elim (fun h => False.elim (hK x hx h)) id,Or.inr⟩)
  have hc : c.clip (K++L)=c.clip K := c.clip_congr _ _
    (by intro x hx;simp only [List.mem_append];exact ⟨fun h => h.elim id (fun h => False.elim (hL x hx h)),Or.inl⟩)
  simpa only [hc] using c.restrict_plug u v (K++L) (hr.trans hu)

/-- This theorem binds the port to the literal original subtree lookup. Both
selected local sides may have arbitrary internal topology and root ancestry. -/
theorem actual_cut_projection (T u v : Tree) (p : RMAF.Vertex) (K L : List Nat)
    (nd : (leaves T).Nodup) (hp : subtree T p=some u)
    (hK : ∀ x∈leaves u, x∉K) (subL : L⊆leaves u) (hu : restrict L u=some v) :
    ∃ c : Port, T=c.plug u ∧ restrict (K++L) T=some ((c.clip K).plug v) ∧
      ∀ x∈leaves u, x∉c.labels := by
  obtain ⟨c,hc⟩ := original_port T u p hp
  have ndC : (c.labels++leaves u).Nodup := (c.leaves_perm u).nodup_iff.1 (hc ▸ nd)
  have sep := (List.nodup_append.1 ndC).2.2
  have hL : ∀ x∈c.labels, x∉L := by
    intro x hx hxl
    exact sep x hx x (subL hxl) rfl
  refine ⟨c,hc,?_,?_⟩
  · rw [hc]
    exact c.restrict_join u v K L hK hL hu
  · intro x hx hxc
    exact sep x hxc x hx rfl

/-- Topology gluing at actual original cuts when the same labelled side is
the descendant side in both trees. The port comparison is an actual restricted
topology premise; it is not a supplied reconstruction property. -/
theorem original_cut_topology_glue (T S uT uS vT vS : Tree)
    (pT pS : RMAF.Vertex) (K L : List Nat) (y : Nat)
    (ndT : (leaves T).Nodup) (ndS : (leaves S).Nodup)
    (hpT : subtree T pT=some uT) (hpS : subtree S pS=some uS)
    (hKT : ∀ x∈leaves uT, x∉K) (hKS : ∀ x∈leaves uS, x∉K)
    (subT : L⊆leaves uT) (subS : L⊆leaves uS)
    (hyT : y∈leaves uT) (hyS : y∈leaves uS)
    (hvT : restrict L uT=some vT) (hvS : restrict L uS=some vS)
    (hi : RootedIso vT vS)
    (htopo : restrictionAgrees T S (K++[y])=true) :
    restrictionAgrees T S (K++L)=true := by
  obtain ⟨c,hc,hcL,sepC⟩ := actual_cut_projection T uT vT pT K L ndT hpT hKT subT hvT
  obtain ⟨d,hd,hdL,sepD⟩ := actual_cut_projection S uS vS pS K L ndS hpS hKS subS hvS
  have nduT : (leaves uT).Nodup := (List.nodup_append.1
    ((c.leaves_perm uT).nodup_iff.1 (hc ▸ ndT))).2.1
  have nduS : (leaves uS).Nodup := (List.nodup_append.1
    ((d.leaves_perm uS).nodup_iff.1 (hd ▸ ndS))).2.1
  have hyc : y∉c.labels := sepC y hyT
  have hyd : y∉d.labels := sepD y hyS
  have hcY : restrict (K++[y]) T=some ((c.clip K).plug (.leaf y)) := by
    rw [hc]
    exact c.restrict_join uT (.leaf y) K [y] hKT
      (by
        intro x hx hxy
        have he : x=y := by simpa using hxy
        subst x
        exact hyc hx)
      (restrict_singleton uT y nduT hyT)
  have hdY : restrict (K++[y]) S=some ((d.clip K).plug (.leaf y)) := by
    rw [hd]
    exact d.restrict_join uS (.leaf y) K [y] hKS
      (by
        intro x hx hxy
        have he : x=y := by simpa using hxy
        subst x
        exact hyd hx)
      (restrict_singleton uS y nduS hyS)
  have hport : RootedIso ((c.clip K).plug (.leaf y)) ((d.clip K).plug (.leaf y)) := by
    apply (sameShape_correct _ _).1
    simpa only [restrictionAgrees,hcY,hdY] using htopo
  have hglue := port_glue_same_orientation (c.clip K) (d.clip K) vT vS y
    (fun h => hyc (c.clip_labels_sub K h)) (fun h => hyd (d.clip_labels_sub K h)) hport hi
  simpa only [restrictionAgrees,hcL,hdL] using
    (sameShape_correct _ _).2 hglue
end OrdinaryCommonSplit
