/- Contacted repair component: distinct cherry-endpoint blocks force a singleton. -/
import CladeControls
open RMAF ForestState Universal233 Universal233.HardParent
open IndependentGeometry IndependentOneExchange ContactedClade
namespace ContactedRepair

theorem subtree_append (T : Tree) (p q : Vertex) :
 CoreGraph.subtree T (p++q)=(CoreGraph.subtree T p).bind (fun U=>CoreGraph.subtree U q) := by
 induction p generalizing T with
 | nil => rfl
 | cons side rest ih =>
  cases T with
  | leaf y => rfl
  | node l r => cases side <;> exact ih _

theorem block_nodup {F : List (List Nat)} (nd : F.flatten.Nodup) {B : List Nat} (hB : B∈F) : B.Nodup := by
 induction F with
 | nil => simp at hB
 | cons A rest ih =>
  have checks := List.nodup_append.1 nd
  rcases List.mem_cons.1 hB with rfl|ht
  · exact checks.1
  · exact ih checks.2.1 ht

theorem different_member {B : List Nat} {a : Nat} (nd : B.Nodup) (ha : a∈B) (different : B≠[a]) :
 ∃x,x∈B ∧ x≠a := by
 cases B with
 | nil => simp at ha
 | cons x xs =>
  by_cases eq : x=a
  · subst x
    cases xs with
    | nil => exact False.elim (different rfl)
    | cons y ys =>
     have no := (List.nodup_cons.1 nd).1
     exact ⟨y,by simp,fun e=>no (by simp [e])⟩
  · exact ⟨x,by simp,eq⟩

theorem endpoint_hull {T : Tree} {p : Vertex} {a b : Nat} (ch : CoreGraph.CherryAt T p a b)
 (side : Bool) {B : List Nat} (endpoint : (if side then b else a)∈B)
 (outside : ∃x,x∈leaves T ∧ x∈B ∧ x≠(if side then b else a)) :
 p∈minimalVertices B T := by
 have sub : CoreGraph.subtree T (p++[side])=some (.leaf (if side then b else a)) := by
  rw [subtree_append,ch]
  cases side <;> rfl
 have hit : ∃x,x∈leaves (.leaf (if side then b else a)) ∧ x∈B :=
  ⟨_,by simp [leaves],endpoint⟩
 have out : ∃x,x∈leaves T ∧ x∈B ∧ x∉leaves (.leaf (if side then b else a)) := by
  obtain ⟨x,xt,xb,ne⟩ := outside
  exact ⟨x,xt,xb,by simpa [leaves] using ne⟩
 simpa using crossing_boundary_in_minimal sub hit out

theorem distinct_endpoint_blocks {T S : Tree} {p : Vertex} {a b : Nat}
 (proper : DepthOne.proper T S=true) (ch : CoreGraph.CherryAt T p a b)
 {F : List (List Nat)} (hF : agreement T S F=true)
 {A B : List Nat} (aF : A∈F) (bF : B∈F) (ha : a∈A) (hb : b∈B) (different : A≠B) :
 A=[a] ∨ B=[b] := by
 have checks := hF
 simp only [agreement,Bool.and_eq_true] at checks
 have part := checks.1.1.1.1
 have nt := (IndependentReconstruction.proper_parts proper).1
 have flat := (IndependentCommon.flatten_from_partition _ F nt part).symm.nodup nt
 have labels : ∀C∈F,∀x∈C,x∈leaves T := by
  simp only [partitionCheck,Bool.and_eq_true] at part
  intro C hC x hx
  exact List.contains_iff_mem.1 (List.all_eq_true.1 part.2 x (List.mem_flatten.2 ⟨C,hC,hx⟩))
 by_cases ea : A=[a]
 · exact Or.inl ea
 · by_cases eb : B=[b]
   · exact Or.inr eb
   · obtain ⟨x,xa,neA⟩ := different_member (block_nodup flat aF) ha ea
     obtain ⟨y,yb,neB⟩ := different_member (block_nodup flat bF) hb eb
     have ap := endpoint_hull ch false ha ⟨x,labels A aF x xa,xa,neA⟩
     have bp := endpoint_hull ch true hb ⟨y,labels B bF y yb,yb,neB⟩
     exact False.elim (different (shared_hull_block_equal checks.1.2 aF bF ap bp))

theorem endpoint_partition_cases {T S : Tree} {p : Vertex} {a b : Nat}
 (proper : DepthOne.proper T S=true) (ch : CoreGraph.CherryAt T p a b)
 {F : List (List Nat)} (hF : agreement T S F=true) :
 [a]∈F ∨ [b]∈F ∨ ∃B∈F,a∈B ∧ b∈B := by
 have part := hF
 simp only [agreement,Bool.and_eq_true] at part
 have aT : a∈leaves T := subtree_leaves_own ch a (by simp [leaves])
 have bT : b∈leaves T := subtree_leaves_own ch b (by simp [leaves])
 obtain ⟨A,aF,ha⟩ := List.mem_flatten.1 (IndependentReconstruction.coverage _ _ part.1.1.1.1 aT)
 obtain ⟨B,bF,hb⟩ := List.mem_flatten.1 (IndependentReconstruction.coverage _ _ part.1.1.1.1 bT)
 by_cases eq : A=B
 · subst A;exact Or.inr (Or.inr ⟨B,bF,ha,hb⟩)
 · rcases distinct_endpoint_blocks proper ch hF aF bF ha hb eq with ea|eb
   · exact Or.inl (ea ▸ aF)
   · exact Or.inr (Or.inl (eb ▸ bF))
end ContactedRepair
