import OriginalPort
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge

theorem Port.empty_labels (c : Port) (h : c.labels=[]) : c=.hole := by
  cases c with
  | hole => rfl
  | left c r =>
    have hr : leaves r=[] := (List.append_eq_nil_iff.1 h).2
    exact False.elim (leaves_nonempty r hr)
  | right l c =>
    have hl : leaves l=[] := (List.append_eq_nil_iff.1 h).1
    exact False.elim (leaves_nonempty l hl)

theorem Port.singleton_labels (c : Port) (x : Nat) (h : c.labels=[x]) :
    c=.left .hole (.leaf x) ∨ c=.right (.leaf x) .hole := by
  cases c with
  | hole => simp [Port.labels] at h
  | left c r =>
    have hp : 0<(leaves r).length := List.length_pos_iff.2 (leaves_nonempty r)
    have hn := congrArg List.length h
    simp only [Port.labels,List.length_append,List.length_singleton] at hn
    have hc0 : c.labels=[] := List.length_eq_zero_iff.1 (by omega)
    have hc : c=.hole := c.empty_labels hc0
    subst c
    have hr : leaves r=[x] := by simpa [Port.labels] using h
    have hre := ForestState.tree_of_singleton_leaves r x hr
    subst r
    exact Or.inl rfl
  | right l c =>
    have hp : 0<(leaves l).length := List.length_pos_iff.2 (leaves_nonempty l)
    have hn := congrArg List.length h
    simp only [Port.labels,List.length_append,List.length_singleton] at hn
    have hc0 : c.labels=[] := List.length_eq_zero_iff.1 (by omega)
    have hc : c=.hole := c.empty_labels hc0
    subst c
    have hl : leaves l=[x] := by simpa [Port.labels] using h
    have hle := ForestState.tree_of_singleton_leaves l x hl
    subst l
    exact Or.inr rfl

theorem Port.clip_labels (c : Port) (U : List Nat) :
    (c.clip U).labels=c.labels.filter (U.contains ·) := by
  induction c with
  | hole => rfl
  | left c r ih =>
    cases hr : restrict U r with
    | none =>
      have hf : (leaves r).filter (U.contains ·)=[] := by
        have h := restrict_leaves r U
        simpa only [hr,optionLeaves] using h.symm
      simp only [Port.clip,hr,Port.labels,List.filter_append,ih,hf,List.append_nil]
    | some v =>
      simp only [Port.clip,hr,Port.labels,List.filter_append,ih,restrict_labels r v U hr]
  | right l c ih =>
    cases hl : restrict U l with
    | none =>
      have hf : (leaves l).filter (U.contains ·)=[] := by
        have h := restrict_leaves l U
        simpa only [hl,optionLeaves] using h.symm
      simp only [Port.clip,hl,Port.labels,List.filter_append,ih,hf,List.nil_append]
    | some v =>
      simp only [Port.clip,hl,Port.labels,List.filter_append,ih,restrict_labels l v U hl]

theorem Port.clip_singleton_shape (c : Port) (x : Nat) (nd : c.labels.Nodup)
    (hx : x∈c.labels) :
    c.clip [x]=.left .hole (.leaf x) ∨ c.clip [x]=.right (.leaf x) .hole := by
  apply Port.singleton_labels
  rw [Port.clip_labels]
  apply ForestState.subset_singleton_eq
  · intro h
    have hm : x∈c.labels.filter ([x].contains ·) := by simp [hx]
    rw [h] at hm
    simp at hm
  · intro y hy
    exact List.contains_iff_mem.1 (List.mem_filter.1 hy).2
  · exact nd.filter _

/-- When one surviving representative lies outside the cut, the literal
restriction is a root join of that representative and the selected subtree.
This handles all original ancestors and both sibling orientations. -/
theorem Port.one_outside_projection (c : Port) (u v : Tree) (K : List Nat) (x : Nat)
    (nd : c.labels.Nodup) (hx : x∈c.labels) (nux : x∉leaves u)
    (subK : K⊆leaves u) (sep : ∀ y∈leaves u, y∉c.labels)
    (hu : restrict K u=some v) :
    ∃ w, restrict (K++[x]) (c.plug u)=some w ∧ RootedIso w (.node v (.leaf x)) := by
  have hbase : restrict ([x]++K) (c.plug u)=some ((c.clip [x]).plug v) :=
    c.restrict_join u v [x] K
      (by
        intro y hy h
        have he : y=x := by simpa using h
        subst y
        exact nux hy)
      (by intro y hy hK;exact sep y (subK hK) hy) hu
  have hcomm : restrict (K++[x]) (c.plug u)=restrict ([x]++K) (c.plug u) :=
    Universal233.DepthOne.restrict_members _ _ _ (by intro y;simp only [List.mem_append];exact or_comm)
  refine ⟨(c.clip [x]).plug v,hcomm.trans hbase,?_⟩
  rcases c.clip_singleton_shape x nd hx with he | he
  · rw [he]
    exact .straight ((sameShape_correct v v).1 (sameShape_refl v)) (.leaf x)
  · rw [he]
    exact .swapped (.leaf x) ((sameShape_correct v v).1 (sameShape_refl v))
end OrdinaryCommonSplit
