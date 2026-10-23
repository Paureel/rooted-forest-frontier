/- A common lift of contracted vertices into original hulls after deleting b. -/
import CoarsenRestrictionV3
open RMAF ForestState Universal233 Universal233.HardParent
namespace IndependentGeometry

def embed (a : Nat) : Tree → Tree → Vertex → Vertex
 | .leaf _, .leaf _, _ => []
 | .leaf _, .node (.leaf x) (.leaf _), _ => if x==a then [false] else [true]
 | .node _ _,.node _ _,[] => []
 | .node l r,.node L R,side::rest =>
   side::embed a (if side then r else l) (if side then R else L) rest
 | _,_,_ => []

theorem empty_from_map {α β : Type} (f : α→β) (new : List α) (old : List β)
 (map : ∀v∈new,f v∈old) (empty : old.isEmpty=true) : new.isEmpty=true := by
 have eo : old=[] := by simpa using empty
 cases new with
 | nil => rfl
 | cons v rest => have impossible := map v (by simp); simp [eo] at impossible

theorem minimal_in_span (T : Tree) (B : List Nat) :
 ∀v∈minimalVertices B T,v∈rootedSpan B T := by
 induction T with
 | leaf x => exact fun v hv=>hv
 | node l r il ir =>
  change ∀v∈(if (rootedSpan B l).isEmpty then prependSide true (minimalVertices B r)
    else if (rootedSpan B r).isEmpty then prependSide false (minimalVertices B l)
    else []::(prependSide false (rootedSpan B l)++prependSide true (rootedSpan B r))),
   v∈(if (rootedSpan B l).isEmpty && (rootedSpan B r).isEmpty then []
    else []::(prependSide false (rootedSpan B l)++prependSide true (rootedSpan B r)))
  cases hl : (rootedSpan B l).isEmpty <;> cases hr : (rootedSpan B r).isEmpty <;>
   simp only [hl,hr,Bool.false_eq_true,Bool.false_and,Bool.true_and,ite_false,ite_true]
  · exact fun v hv=>hv
  · intro v hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
    exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.2 ⟨w,il w hw,rfl⟩))
  · intro v hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
    exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.2 ⟨w,ir w hw,rfl⟩))
  · intro v hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
    have member := ir w hw
    have empty : rootedSpan B r=[] := by simpa using hr
    simp [empty] at member

theorem span_shrink_lift {a b z : Nat} {C T : Tree} (h : Grow a b z C T)
 (ab : a≠b) (B : List Nat) (nz : z∉B) :
 ∀v∈rootedSpan (shrinkBlock a b z B) C,embed a C T v∈rootedSpan B T := by
 induction h with
 | @fixed x xa xb xz =>
  have sf : x∈shrinkBlock a b z B ↔ x∈B := by
   simpa only [List.contains_iff_mem] using Bool.eq_iff_iff.1 (shrink_fixed_contains B xa xb xz)
  by_cases hx : x∈B <;> simp [rootedSpan,sf,hx,embed]
 | cherry =>
  have sm : z∈shrinkBlock a b z B ↔ a∈B := by
   simpa only [List.contains_iff_mem] using Bool.eq_iff_iff.1 (shrink_z_contains B ab nz)
  by_cases ha : a∈B <;> by_cases hb : b∈B <;> simp [rootedSpan,sm,ha,hb,embed,prependSide]
 | swapped =>
  have sm : z∈shrinkBlock a b z B ↔ a∈B := by
   simpa only [List.contains_iff_mem] using Bool.eq_iff_iff.1 (shrink_z_contains B ab nz)
  by_cases ha : a∈B <;> by_cases hb : b∈B <;> simp [rootedSpan,sm,ha,hb,embed,prependSide,Ne.symm ab]
 | @node l r L R hl hr il ir =>
  change ∀v∈(if (rootedSpan (shrinkBlock a b z B) l).isEmpty &&
   (rootedSpan (shrinkBlock a b z B) r).isEmpty then [] else
   []::(prependSide false (rootedSpan (shrinkBlock a b z B) l)++prependSide true (rootedSpan (shrinkBlock a b z B) r))),
   embed a (.node l r) (.node L R) v∈rootedSpan B (.node L R)
  split
  · simp
  · rename_i active
    have oldActive : ((rootedSpan B L).isEmpty && (rootedSpan B R).isEmpty)=false := by
     cases eq : ((rootedSpan B L).isEmpty && (rootedSpan B R).isEmpty) with
     | false => rfl
     | true =>
      have parts : (rootedSpan B L).isEmpty=true ∧ (rootedSpan B R).isEmpty=true := by simpa only [Bool.and_eq_true] using eq
      have el := empty_from_map (embed a l L) _ _ il parts.1
      have er := empty_from_map (embed a r R) _ _ ir parts.2
      simp [el,er] at active
    simp only [rootedSpan,oldActive,Bool.false_eq_true,ite_false]
    intro v hv
    rcases List.mem_cons.1 hv with rfl|hv
    · simp [embed]
    · rcases List.mem_append.1 hv with hv|hv
      · obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
        exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.2 ⟨embed a l L w,il w hw,rfl⟩))
      · obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
        exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.2 ⟨embed a r R w,ir w hw,rfl⟩))

end IndependentGeometry
