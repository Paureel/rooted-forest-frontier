import PortContract
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge

theorem relabel_fixed (f : Nat→Nat) (t : Tree) (h : ∀x∈leaves t,f x=x) : relabel f t=t := by
  induction t with
  | leaf x => simp only [relabel,h x (by simp [leaves])]
  | node a b ha hb =>
    simp only [relabel,ha (by intro x hx;exact h x (List.mem_append_left _ hx)),
      hb (by intro x hx;exact h x (List.mem_append_right _ hx))]

theorem Port.relabel_hole (c : Port) (f : Nat→Nat) (y : Nat)
    (h : ∀x∈c.labels,f x=x) : relabel f (c.plug (.leaf y))=c.plug (.leaf (f y)) := by
  induction c with
  | hole => rfl
  | left c r ih =>
    simp only [Port.plug,relabel,ih (by intro x hx;exact h x (List.mem_append_left _ hx)),
      relabel_fixed f r (by intro x hx;exact h x (List.mem_append_right _ hx))]
  | right l c ih =>
    simp only [Port.plug,relabel,ih (by intro x hx;exact h x (List.mem_append_right _ hx)),
      relabel_fixed f l (by intro x hx;exact h x (List.mem_append_left _ hx))]

/-- Source descendant-side original projection. Every tree/port on the right
is produced by literal restriction, and an arbitrary representative in the
contracted side gives the same explicit fresh-marker topology. -/
theorem Port.contract_desc_projection (c : Port) (u v : Tree) (Y K L : List Nat) (y m : Nat)
    (nd : (leaves (c.plug u)).Nodup) (hu : leaves u⊆Y)
    (hc : ∀x∈c.labels,x∉Y) (subK : K⊆c.labels) (subL : L⊆leaves u)
    (hy : y∈leaves u) (fresh : m∉leaves (c.plug u)) (hv : restrict L u=some v) :
    ∃ a z, restrict (K++L) (c.plug u)=some a ∧
      restrict (K++[y]) (c.plug u)=some z ∧
      contract Y m a=relabel (swap y m) z := by
  have ndc := List.nodup_append.1 ((c.leaves_perm u).nodup_iff.1 nd)
  have sep : ∀x∈leaves u,x∉c.labels := by
    intro x hx hxc;exact ndc.2.2 x hxc x hx rfl
  have fC : m∉c.labels := by
    intro hm
    exact fresh ((c.leaves_perm u).mem_iff.2 (List.mem_append_left _ hm))
  have hK : ∀x∈leaves u,x∉K := by
    intro x hx hxK;exact hc x (subK hxK) (hu hx)
  have hL : ∀x∈c.labels,x∉L := by
    intro x hx hxL;exact sep x (subL hxL) hx
  have hKy : ∀x∈c.labels,x∉[y] := by
    intro x hx hxY
    have he : x=y := by simpa using hxY
    subst x
    exact sep y hy hx
  have a := c.restrict_join u v K L hK hL hv
  have z := c.restrict_join u (.leaf y) K [y] hK hKy
    (restrict_singleton u y ndc.2.1 hy)
  refine ⟨(c.clip K).plug v,(c.clip K).plug (.leaf y),a,z,?_⟩
  have hvY : leaves v⊆Y := fun _ hx => hu ((restricted_labels_exact u v L hv).1 hx).1
  have clipNo : ∀x∈(c.clip K).labels,x∉Y := fun x hx => hc x (c.clip_labels_sub K hx)
  have clipFresh : m∉(c.clip K).labels := fun hx => fC (c.clip_labels_sub K hx)
  rw [Port.contract_hole _ v Y m hvY clipNo clipFresh,
    Port.relabel_hole _ (swap y m) y]
  · simp [swap]
  · intro x hx
    exact swap_fixes y m x
      (by intro he;subst x;exact sep y hy (c.clip_labels_sub K hx))
      (by intro he;subst x;exact clipFresh hx)

/-- The complementary original root-side orientation uses the same total
contraction. All surviving ancestor branches normalize to one attachment, so
the result does not depend on which actual complementary representative was
selected. -/
theorem Port.contract_root_projection (c : Port) (u v : Tree) (Y K L : List Nat) (y m : Nat)
    (nd : (leaves (c.plug u)).Nodup) (hu : ∀x∈leaves u,x∉Y)
    (hc : c.labels⊆Y) (subK : K⊆leaves u) (subL : L⊆c.labels) (neL : L≠[])
    (hy : y∈c.labels) (fresh : m∉leaves (c.plug u)) (hv : restrict K u=some v) :
    ∃ a z, restrict (K++L) (c.plug u)=some a ∧
      restrict (K++[y]) (c.plug u)=some z ∧
      RootedIso (contract Y m a) (relabel (swap y m) z) := by
  have ndc := List.nodup_append.1 ((c.leaves_perm u).nodup_iff.1 nd)
  have sep : ∀x∈leaves u,x∉c.labels := by
    intro x hx hxc;exact ndc.2.2 x hxc x hx rfl
  have fu : m∉leaves u := by
    intro hm
    exact fresh ((c.leaves_perm u).mem_iff.2 (List.mem_append_right _ hm))
  have hLy : ∀x∈leaves u,x∉L := by
    intro x hx hxL;exact hu x hx (hc (subL hxL))
  have hK : ∀x∈c.labels,x∉K := by
    intro x hx hxK;exact sep x (subK hxK) hx
  have a : restrict (K++L) (c.plug u)=some ((c.clip L).plug v) := by
    have hcomm : restrict (K++L) (c.plug u)=restrict (L++K) (c.plug u) :=
      Universal233.DepthOne.restrict_members _ _ _ (by intro x;simp only [List.mem_append];exact or_comm)
    exact hcomm.trans (c.restrict_join u v L K hLy hK hv)
  have nyu : y∉leaves u := fun hyu => sep y hyu hy
  obtain ⟨z,hz,hzi⟩ := c.one_outside_projection u v K y ndc.1 hy nyu subK sep hv
  refine ⟨(c.clip L).plug v,z,a,hz,?_⟩
  have nv : ∀x∈leaves v,x∉Y := fun x hx => hu x ((restricted_labels_exact u v K hv).1 hx).1
  have fv : m∉leaves v := fun hx => fu ((restricted_labels_exact u v K hv).1 hx).1
  have nc : c.clip L≠.hole := by
    obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil L neL
    have hm : x∈(c.clip L).labels := by rw [Port.clip_labels];simp [subL hx,hx]
    intro he
    rw [he] at hm
    simp [Port.labels] at hm
  have contractIso := Port.contract_complement (c.clip L) v Y m nv
    (fun _ hx => hc (c.clip_labels_sub L hx)) fv nc
  have relabelV : relabel (swap y m) v=v := relabel_fixed _ v (by
    intro x hx
    exact swap_fixes y m x
      (by intro he;subst x;exact nyu ((restricted_labels_exact u v K hv).1 hx).1)
      (by intro he;subst x;exact fv hx))
  have zi : RootedIso (relabel (swap y m) z) (.node v (.leaf m)) := by
    have hi := relabel_iso (swap y m) hzi
    simpa only [relabel,relabelV,swap,ite_true] using hi
  exact rootedIso_trans contractIso (BinaryExchange.iso_symm zi)

end OrdinaryCommonSplit
