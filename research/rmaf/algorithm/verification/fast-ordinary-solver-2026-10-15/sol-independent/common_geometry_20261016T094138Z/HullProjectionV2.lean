/- Independent common collapse of original embedding vertices. -/
import RestrictionGrowV2
open RMAF ForestState Universal233 Universal233.HardParent
namespace IndependentGeometry

def project : Tree → Vertex → Vertex
 | .leaf _,_ => []
 | .node _ _,[] => []
 | .node l r,side::rest => side::project (if side then r else l) rest

theorem span_empty_grow {a b z : Nat} {C T : Tree} (h : Grow a b z C T)
 (B : List Nat) (na : a∉B) (nb : b∉B) :
 (rootedSpan (expandBlock a b z B) T).isEmpty=(rootedSpan B C).isEmpty := by
 induction h with
 | fixed xa xb xz => simp only [rootedSpan,fixed_contains B xa xb xz]
 | cherry =>
  have ep := endpoint_contains B a b z na nb
  have ea : a∈expandBlock a b z B ↔ z∈B := by simpa only [List.contains_iff_mem] using Bool.eq_iff_iff.1 ep.1
  have eb : b∈expandBlock a b z B ↔ z∈B := by simpa only [List.contains_iff_mem] using Bool.eq_iff_iff.1 ep.2
  by_cases hz : z∈B <;> simp [rootedSpan,ea,eb,hz,prependSide]
 | swapped =>
  have ep := endpoint_contains B a b z na nb
  have ea : a∈expandBlock a b z B ↔ z∈B := by simpa only [List.contains_iff_mem] using Bool.eq_iff_iff.1 ep.1
  have eb : b∈expandBlock a b z B ↔ z∈B := by simpa only [List.contains_iff_mem] using Bool.eq_iff_iff.1 ep.2
  by_cases hz : z∈B <;> simp [rootedSpan,ea,eb,hz,prependSide]
 | node hl hr il ir =>
  simp only [rootedSpan,il,ir]
  split <;> rfl

theorem prepend_project {C : Tree} {side : Bool} {old new : List Vertex}
 (h : ∀v∈new,project C v∈old) {v : Vertex}
 (hv : v∈prependSide side new) :
 side::project C v.tail∈prependSide side old := by
 obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
 exact List.mem_map.2 ⟨project C w,h w hw,rfl⟩

theorem span_projects {a b z : Nat} {C T : Tree} (h : Grow a b z C T)
 (B : List Nat) (na : a∉B) (nb : b∉B) :
 ∀v∈rootedSpan (expandBlock a b z B) T,project C v∈rootedSpan B C := by
 induction h with
 | fixed xa xb xz =>
  simp only [rootedSpan,fixed_contains B xa xb xz]
  split
  · intro v hv; simp [project]
  · simp
 | cherry =>
  have ep := endpoint_contains B a b z na nb
  have ea : a∈expandBlock a b z B ↔ z∈B := by simpa only [List.contains_iff_mem] using Bool.eq_iff_iff.1 ep.1
  have eb : b∈expandBlock a b z B ↔ z∈B := by simpa only [List.contains_iff_mem] using Bool.eq_iff_iff.1 ep.2
  by_cases hz : z∈B <;> simp [rootedSpan,ea,eb,hz,prependSide,project]
 | swapped =>
  have ep := endpoint_contains B a b z na nb
  have ea : a∈expandBlock a b z B ↔ z∈B := by simpa only [List.contains_iff_mem] using Bool.eq_iff_iff.1 ep.1
  have eb : b∈expandBlock a b z B ↔ z∈B := by simpa only [List.contains_iff_mem] using Bool.eq_iff_iff.1 ep.2
  by_cases hz : z∈B <;> simp [rootedSpan,ea,eb,hz,prependSide,project]
 | @node l r L R hl hr il ir =>
  have el := span_empty_grow hl B na nb
  have er := span_empty_grow hr B na nb
  simp only [rootedSpan,el,er]
  split
  · simp
  · intro v hv
    rcases List.mem_cons.1 hv with rfl|hv
    · simp [project]
    · rcases List.mem_append.1 hv with hv|hv
      · obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
        exact List.mem_cons_of_mem _ (List.mem_append_left _
         (List.mem_map.2 ⟨project l w,il w hw,rfl⟩))
      · obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
        exact List.mem_cons_of_mem _ (List.mem_append_right _
         (List.mem_map.2 ⟨project r w,ir w hw,rfl⟩))

theorem minimal_projects {a b z : Nat} {C T : Tree} (h : Grow a b z C T)
 (B : List Nat) (na : a∉B) (nb : b∉B) :
 ∀v∈minimalVertices (expandBlock a b z B) T,project C v∈minimalVertices B C := by
 induction h with
 | fixed xa xb xz =>
  simp only [minimalVertices,fixed_contains B xa xb xz]
  split
  · intro v hv; simp [project]
  · simp
 | cherry =>
  have ep := endpoint_contains B a b z na nb
  have ea : a∈expandBlock a b z B ↔ z∈B := by simpa only [List.contains_iff_mem] using Bool.eq_iff_iff.1 ep.1
  have eb : b∈expandBlock a b z B ↔ z∈B := by simpa only [List.contains_iff_mem] using Bool.eq_iff_iff.1 ep.2
  by_cases hz : z∈B <;> simp [minimalVertices,rootedSpan,ea,eb,hz,prependSide,project]
 | swapped =>
  have ep := endpoint_contains B a b z na nb
  have ea : a∈expandBlock a b z B ↔ z∈B := by simpa only [List.contains_iff_mem] using Bool.eq_iff_iff.1 ep.1
  have eb : b∈expandBlock a b z B ↔ z∈B := by simpa only [List.contains_iff_mem] using Bool.eq_iff_iff.1 ep.2
  by_cases hz : z∈B <;> simp [minimalVertices,rootedSpan,ea,eb,hz,prependSide,project]
 | @node l r L R hl hr il ir =>
  have el := span_empty_grow hl B na nb
  have er := span_empty_grow hr B na nb
  simp only [minimalVertices,el,er]
  split
  · intro v hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
    exact List.mem_map.2 ⟨project r w,ir w hw,rfl⟩
  · split
    · intro v hv
      obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
      exact List.mem_map.2 ⟨project l w,il w hw,rfl⟩
    · intro v hv
      rcases List.mem_cons.1 hv with rfl|hv
      · simp [project]
      · rcases List.mem_append.1 hv with hv|hv
        · obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
          exact List.mem_cons_of_mem _ (List.mem_append_left _
           (List.mem_map.2 ⟨project l w,span_projects hl B na nb w hw,rfl⟩))
        · obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hv
          exact List.mem_cons_of_mem _ (List.mem_append_right _
           (List.mem_map.2 ⟨project r w,span_projects hr B na nb w hw,rfl⟩))
end IndependentGeometry
