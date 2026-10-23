import Restriction
import Executable
open RMAF
namespace Universal233.HardParent.CommonCherryZero

private theorem pair_contains_left (a b : Nat) : [a,b].contains a = true := by
  simp only [List.contains_cons, List.contains_nil, beq_self_eq_true, Bool.true_or]
private theorem pair_contains_right (a b : Nat) : [a,b].contains b = true := by
  simp only [List.contains_cons, List.contains_nil, beq_self_eq_true, Bool.or_true, Bool.or_false]

private theorem cherry_members {a b : Nat} {S : Tree} (h : HasCherry a b S) :
    a ∈ leaves S ∧ b ∈ leaves S := by
  induction h with
  | here => simp only [leaves, List.mem_append, List.mem_singleton, true_or, or_true, and_self]
  | swap => simp only [leaves, List.mem_append, List.mem_singleton, true_or, or_true, and_self]
  | left h ih =>
    exact ⟨List.mem_append_left _ ih.1, List.mem_append_left _ ih.2⟩
  | right h ih =>
    exact ⟨List.mem_append_right _ ih.1, List.mem_append_right _ ih.2⟩

private theorem cherry_span {a b : Nat} {S : Tree} (h : HasCherry a b S) :
    (rootedSpan [a,b] S).isEmpty = false := by
  induction h with
  | here => simp only [rootedSpan, pair_contains_left, pair_contains_right]; rfl
  | swap => simp only [rootedSpan, pair_contains_left, pair_contains_right]; rfl
  | left h ih => simp only [rootedSpan, ih, Bool.false_and]; rfl
  | right h ih => simp only [rootedSpan, ih, Bool.and_false]; rfl

private theorem span_empty {a b : Nat} (S : Tree)
    (ha : a ∉ leaves S) (hb : b ∉ leaves S) : rootedSpan [a,b] S = [] := by
  induction S with
  | leaf x =>
    cases hc : [a,b].contains x with
    | false => simp only [rootedSpan, hc]; rfl
    | true =>
      have hx := List.contains_iff_mem.mp hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx
      · exact False.elim (ha (by rw [leaves, List.mem_singleton]; exact hx.symm))
      · exact False.elim (hb (by rw [leaves, List.mem_singleton]; exact hx.symm))
  | node l r il ir =>
    have hal : a ∉ leaves l := fun h => ha (List.mem_append_left _ h)
    have har : a ∉ leaves r := fun h => ha (List.mem_append_right _ h)
    have hbl : b ∉ leaves l := fun h => hb (List.mem_append_left _ h)
    have hbr : b ∉ leaves r := fun h => hb (List.mem_append_right _ h)
    simp only [rootedSpan, il hal hbl, ir har hbr]; rfl

private theorem contains_lift (side : Bool) (vs : List Vertex) (v : Vertex) :
    (prependSide side vs).contains (side :: v) = vs.contains v := by
  induction vs with
  | nil => rfl
  | cons w ws ih =>
    simp only [prependSide, List.map_cons, List.contains_cons, List.cons_beq_cons,
      beq_self_eq_true, Bool.true_and]
    change (v == w || (prependSide side ws).contains (side :: v)) = (v == w || ws.contains v)
    rw [ih]

private theorem contains_lift_nil (side : Bool) (vs : List Vertex) :
    (prependSide side vs).contains [] = false := by
  induction vs with
  | nil => rfl
  | cons w ws ih =>
    change (false || (prependSide side ws).contains []) = false
    exact ih

private theorem contains_lift_other (side : Bool) (vs : List Vertex) (v : Vertex) :
    (prependSide side vs).contains ((!side) :: v) = false := by
  induction vs with
  | nil => rfl
  | cons w ws ih =>
    cases side with
    | false =>
      change (false || (prependSide false ws).contains (true :: v)) = false
      exact ih
    | true =>
      change (false || (prependSide true ws).contains (false :: v)) = false
      exact ih

private def cut (vs : List Vertex) (v : Vertex) : Bool :=
  !v.isEmpty && vs.contains v.dropLast && !(vs.contains v)
private theorem cut_nil (vs : List Vertex) : cut vs [] = false := rfl
private theorem cut_lift (side : Bool) (vs : List Vertex) (v : Vertex) :
    cut (prependSide side vs) (side :: v) = cut vs v := by
  cases v with
  | nil =>
    change ((prependSide side vs).contains [] &&
      !((prependSide side vs).contains [side])) = false
    rw [contains_lift_nil]; rfl
  | cons x xs =>
    simp only [cut, List.isEmpty_cons, List.dropLast_cons_cons,
      contains_lift, Bool.not_false, Bool.true_and]
private theorem cut_lift_other (side : Bool) (vs : List Vertex) (v : Vertex) :
    cut (prependSide side vs) ((!side) :: v) = false := by
  cases v with
  | nil =>
    change ((prependSide side vs).contains [] &&
      !((prependSide side vs).contains [!side])) = false
    rw [contains_lift_nil]; rfl
  | cons x xs =>
    simp only [cut, List.isEmpty_cons, List.dropLast_cons_cons,
      contains_lift_other, Bool.not_false, Bool.true_and, Bool.false_and]

private theorem lift_left_zero (l r : Tree) (vs : List Vertex)
    (zero : (vertices l).filter (cut vs) = []) :
    (vertices (.node l r)).filter (cut (prependSide false vs)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro v hv hp
  simp only [vertices, List.mem_cons, List.mem_append, prependSide, List.mem_map] at hv
  rcases hv with hv | hv | hv
  · subst v
    simp only [cut_nil, Bool.false_eq_true] at hp
  · rcases hv with ⟨w, hw, rfl⟩
    rw [cut_lift] at hp
    exact (List.filter_eq_nil_iff.mp zero) w hw hp
  · rcases hv with ⟨w, hw, rfl⟩
    change cut (prependSide false vs) ((!false) :: w) = true at hp
    rw [cut_lift_other] at hp
    cases hp

private theorem lift_right_zero (l r : Tree) (vs : List Vertex)
    (zero : (vertices r).filter (cut vs) = []) :
    (vertices (.node l r)).filter (cut (prependSide true vs)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro v hv hp
  simp only [vertices, List.mem_cons, List.mem_append, prependSide, List.mem_map] at hv
  rcases hv with hv | hv | hv
  · subst v
    simp only [cut_nil, Bool.false_eq_true] at hp
  · rcases hv with ⟨w, hw, rfl⟩
    change cut (prependSide true vs) ((!true) :: w) = true at hp
    rw [cut_lift_other] at hp
    cases hp
  · rcases hv with ⟨w, hw, rfl⟩
    rw [cut_lift] at hp
    exact (List.filter_eq_nil_iff.mp zero) w hw hp

/-- Generic original-tree zero-pendant-cuts fact. No selected safety, admission,
    branch-cover, Priority, ordinary exactness or source-cost premise is used. -/
theorem pendantOriginal_eq_nil {S : Tree} {a b : Nat}
    (proper : (leaves S).Nodup) (cherry : HasCherry a b S) :
    pendantOriginal S a b = [] := by
  revert proper
  induction cherry with
  | here =>
    intro proper
    simp only [pendantOriginal, vertices, minimalVertices, rootedSpan,
      pair_contains_left, pair_contains_right, prependSide]
    rfl
  | swap =>
    intro proper
    simp only [pendantOriginal, vertices, minimalVertices, rootedSpan,
      pair_contains_left, pair_contains_right, prependSide]
    rfl
  | @left l r h ih =>
    intro proper
    have nd := List.nodup_append.mp proper
    have mem := cherry_members h
    have har : a ∉ leaves r := fun hr => nd.2.2 a mem.1 a hr rfl
    have hbr : b ∉ leaves r := fun hr => nd.2.2 b mem.2 b hr rfl
    have hs := span_empty r har hbr
    have hn := cherry_span h
    have hm : minimalVertices [a,b] (.node l r) = prependSide false (minimalVertices [a,b] l) := by
      simp only [minimalVertices, hn, hs]; rfl
    unfold pendantOriginal
    rw [hm]
    exact lift_left_zero l r _ (ih nd.1)
  | @right l r h ih =>
    intro proper
    have nd := List.nodup_append.mp proper
    have mem := cherry_members h
    have hal : a ∉ leaves l := fun hl => nd.2.2 a hl a mem.1 rfl
    have hbl : b ∉ leaves l := fun hl => nd.2.2 b hl b mem.2 rfl
    have hs := span_empty l hal hbl
    have hn := cherry_span h
    have hm : minimalVertices [a,b] (.node l r) = prependSide true (minimalVertices [a,b] r) := by
      simp only [minimalVertices, hs]; rfl
    unfold pendantOriginal
    rw [hm]
    exact lift_right_zero l r _ (ih nd.2.1)

end Universal233.HardParent.CommonCherryZero

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @Universal233.HardParent.CommonCherryZero.pendantOriginal_eq_nil
#print axioms Universal233.HardParent.CommonCherryZero.pendantOriginal_eq_nil
