/- Contacted repair component: derive both core-cherry hypotheses before merging. -/
import CoreCleanV2
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open IndependentGeometry IndependentOneExchange ContactedClade
namespace ContactedRepair

theorem leaf_witness (T : Tree) : ∃x,x∈leaves T := by
 induction T with
 | leaf x => exact ⟨x,by simp [leaves]⟩
 | node l r il ir => obtain ⟨x,hx⟩ := il;exact ⟨x,List.mem_append_left _ hx⟩

theorem single_label_tree {T : Tree} {a : Nat} (nd : (leaves T).Nodup)
 (only : ∀x∈leaves T,x=a) : T=.leaf a := by
 cases T with
 | leaf x => have eq := only x (by simp [leaves]);subst x;rfl
 | node l r =>
  obtain ⟨x,xl⟩ := leaf_witness l
  obtain ⟨y,yr⟩ := leaf_witness r
  have xa := only x (List.mem_append_left _ xl)
  have ya := only y (List.mem_append_right _ yr)
  exact False.elim ((List.nodup_append.1 nd).2.2 x xl y yr (xa.trans ya.symm))

theorem binary_two_labels {l r : Tree} {a b : Nat} (nd : (leaves (.node l r)).Nodup)
 (ar : a∈leaves l) (br : b∈leaves r)
 (only : ∀x∈leaves (.node l r),x=a∨x=b) : l=.leaf a ∧ r=.leaf b := by
 have ns := List.nodup_append.1 nd
 constructor
 · apply single_label_tree ns.1
   intro x hx
   rcases only x (List.mem_append_left _ hx) with eq|eq
   · exact eq
   · exact False.elim (ns.2.2 x hx b br eq)
 · apply single_label_tree ns.2.1
   intro x hx
   rcases only x (List.mem_append_right _ hx) with eq|eq
   · exact False.elim (ns.2.2 a ar x hx eq.symm)
   · exact eq

theorem two_label_tree_cherry {T : Tree} {a b : Nat} (nd : (leaves T).Nodup)
 (ab : a≠b) (aT : a∈leaves T) (bT : b∈leaves T)
 (only : ∀x∈leaves T,x=a∨x=b) : HasCherry a b T := by
 cases T with
 | leaf x =>
  have ax : a=x := by simpa [leaves] using aT
  have bx : b=x := by simpa [leaves] using bT
  exact False.elim (ab (ax.trans bx.symm))
 | node l r =>
  obtain ⟨x,xl⟩ := leaf_witness l
  obtain ⟨y,yr⟩ := leaf_witness r
  have xab := only x (List.mem_append_left _ xl)
  have yab := only y (List.mem_append_right _ yr)
  rcases xab with rfl|rfl <;> rcases yab with rfl|rfl
  · exact False.elim ((List.nodup_append.1 nd).2.2 a xl a yr rfl)
  · obtain ⟨eqL,eqR⟩ := binary_two_labels nd xl yr only
    subst l;subst r;exact .here
  · have reversed : ∀x∈leaves (.node l r),x=b∨x=a := fun x hx=>(only x hx).symm
    obtain ⟨eqL,eqR⟩ := binary_two_labels nd xl yr reversed
    subst l;subst r;exact .swap
  · exact False.elim ((List.nodup_append.1 nd).2.2 b xl b yr rfl)

theorem clean_two_labels_cherry (T : Tree) {a b : Nat} {D : List Nat}
 (cl : Clean [a,b] D T) (nd : (leaves T).Nodup) (ab : a≠b)
 (aT : a∈leaves T) (bT : b∈leaves T)
 (cover : ∀x∈leaves T,x=a∨x=b∨x∈D) : HasCherry a b T := by
 induction T with
 | leaf x =>
  have ax : a=x := by simpa [leaves] using aT
  have bx : b=x := by simpa [leaves] using bT
  exact False.elim (ab (ax.trans bx.symm))
 | node l r il ir =>
  have ns := List.nodup_append.1 nd
  rcases cl with ⟨ar,cl⟩|⟨al,cr⟩|noD
  · have left_a : a∈leaves l := by
     rcases List.mem_append.1 aT with h|h
     · exact h
     · exact False.elim (ar a h (by simp))
    have left_b : b∈leaves l := by
     rcases List.mem_append.1 bT with h|h
     · exact h
     · exact False.elim (ar b h (by simp))
    exact .left (il cl ns.1 left_a left_b (fun x hx=>cover x (List.mem_append_left _ hx)))
  · have right_a : a∈leaves r := by
     rcases List.mem_append.1 aT with h|h
     · exact False.elim (al a h (by simp))
     · exact h
    have right_b : b∈leaves r := by
     rcases List.mem_append.1 bT with h|h
     · exact False.elim (al b h (by simp))
     · exact h
    exact .right (ir cr ns.2.1 right_a right_b (fun x hx=>cover x (List.mem_append_right _ hx)))
  · apply two_label_tree_cherry nd ab aT bT
    intro x hx
    rcases cover x hx with h|h|h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (noD x hx h)

theorem source_core_cherry_one {T S U : Tree} {q p : Vertex} {a b : Nat}
 (proper : DepthOne.proper T S=true) (ch : CoreGraph.CherryAt T q a b)
 (one : cuts S a b=[p]) (sub : CoreGraph.subtree S p=some U) :
 ∃R,restrict (coreLabels S a b) S=some R ∧ HasCherry a b R := by
 obtain ⟨nt,ns,perm⟩ := IndependentReconstruction.proper_parts proper
 have aT := subtree_leaves_own ch a (by simp [leaves])
 have bT := subtree_leaves_own ch b (by simp [leaves])
 have aS := perm.mem_iff.1 aT
 have bS := perm.mem_iff.1 bT
 have ep := core_endpoints_one one sub aS bS
 have ab : a≠b := by
  obtain ⟨rest,normal,_⟩ := IndependentCommon.contraction_normal (IndependentCommon.address_to_syntax ch) 0 nt
  intro eq
  exact (List.nodup_cons.1 (normal.nodup nt)).1 (by simp [eq])
 cases hR : restrict (coreLabels S a b) S with
 | none => exact False.elim (restrict_none_absent S _ hR a aS ep.1)
 | some R =>
  refine ⟨R,hR,?_⟩
  have nd : (leaves R).Nodup := by
   have eq := restrict_leaves_eq S (coreLabels S a b)
   simp only [hR,optionLeaves] at eq
   rw [eq]
   exact List.Nodup.filter _ ns
  have labels : ∀x,x∈leaves R↔x∈leaves S ∧ x∈coreLabels S a b := by
   intro x;simpa only [hR,optionLeaves] using restrict_labels S (coreLabels S a b) x
  have subA : ∀x∈[a,b],x∈coreLabels S a b := by
   intro x hx
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
   exact hx.elim (fun e=>e ▸ ep.1) (fun e=>e ▸ ep.2)
  have subD : ∀x∈coreRemainder S a b,x∈coreLabels S a b := fun x hx=>(List.mem_filter.1 hx).1
  have clean := (clean_restrict S _ [a,b] _ subA subD R hR).1 (source_core_clean S a b)
  apply clean_two_labels_cherry R clean nd ab ((labels a).2 ⟨aS,ep.1⟩) ((labels b).2 ⟨bS,ep.2⟩)
  intro x hx
  by_cases xa : x=a
  · exact Or.inl xa
  · by_cases xb : x=b
    · exact Or.inr (Or.inl xb)
    · exact Or.inr (Or.inr (List.mem_filter.2 ⟨((labels x).1 hx).2,by simp [xa,xb]⟩))

theorem restricted_pair_proper {T S R Q : Tree} (proper : DepthOne.proper T S=true)
 (A : List Nat) (ht : restrict A T=some R) (hs : restrict A S=some Q) :
 DepthOne.proper R Q=true := by
 obtain ⟨nt,ns,perm⟩ := IndependentReconstruction.proper_parts proper
 have et := restrict_leaves_eq T A
 have es := restrict_leaves_eq S A
 simp only [ht,optionLeaves] at et
 simp only [hs,optionLeaves] at es
 have rt : (leaves R).Nodup := by rw [et];exact List.Nodup.filter _ nt
 have rs : (leaves Q).Nodup := by rw [es];exact List.Nodup.filter _ ns
 have rp : (leaves R).Perm (leaves Q) := by rw [et,es];exact perm.filter _
 simpa only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using And.intro rt (And.intro rs rp)

theorem shared_core_cherry_one {T S U : Tree} {q p : Vertex} {a b : Nat}
 (proper : DepthOne.proper T S=true) (ch : CoreGraph.CherryAt T q a b)
 (one : cuts S a b=[p]) (sub : CoreGraph.subtree S p=some U) :
 ∃R Q,restrict (coreLabels S a b) T=some R ∧ restrict (coreLabels S a b) S=some Q ∧
 DepthOne.proper R Q=true ∧ HasCherry a b R ∧ HasCherry a b Q := by
 obtain ⟨R,ht,ct⟩ := target_core_cherry_one proper ch one sub
 obtain ⟨Q,hs,cs⟩ := source_core_cherry_one proper ch one sub
 exact ⟨R,Q,ht,hs,restricted_pair_proper proper _ ht hs,ct,cs⟩
end ContactedRepair
