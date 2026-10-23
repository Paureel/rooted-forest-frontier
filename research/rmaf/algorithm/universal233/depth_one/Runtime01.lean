import Witness01

namespace Universal233.DepthOne
open RMAF CoreGraph

def treeSize : Tree → Nat
  | .leaf _ => 1
  | .node l r => 1 + treeSize l + treeSize r

theorem treeSize_pos (S : Tree) : 0 < treeSize S := by cases S <;> simp [treeSize]; omega

theorem vertices_length (S : Tree) : (vertices S).length = treeSize S := by
  induction S with
  | leaf x => simp [vertices,treeSize]
  | node l r hl hr => simp [vertices,treeSize,hl,hr,Nat.add_assoc]; omega

theorem edges_length (S : Tree) : (edges S).length + 1 = treeSize S := by
  cases S <;> simp [edges,treeSize,vertices_length] <;> omega

theorem candidates_length (S : Tree) : (candidates S).length = treeSize S := by
  have h := edges_length S
  simp only [candidates,List.length_cons,List.length_map]
  omega

theorem treeSize_leaves (S : Tree) : treeSize S + 1 = 2 * (leaves S).length := by
  induction S with
  | leaf x => simp [treeSize,leaves]
  | node l r hl hr => simp only [treeSize,leaves,List.length_append,Nat.mul_add]; omega

theorem candidate_count_original_edges (S : Tree) :
    (candidates S).length + 1 = 2 * (leaves S).length := by rw [candidates_length,treeSize_leaves]

theorem vertex_depth (S : Tree) (p : Vertex) (hp : p ∈ vertices S) : p.length + 1 ≤ treeSize S := by
  induction S generalizing p with
  | leaf x => have he : p = [] := by simpa [vertices] using hp
              simp [he,treeSize]
  | node l r hl hr =>
    simp only [vertices,List.mem_cons,List.mem_append,List.mem_map] at hp
    rcases hp with he | ⟨q,hq,he⟩ | ⟨q,hq,he⟩
    · simp [he,treeSize]; omega
    · subst p
      have h := hl q hq
      have hpos := treeSize_pos r
      simp only [List.length_cons,treeSize]
      omega
    · subst p
      have h := hr q hq
      have hpos := treeSize_pos l
      simp only [List.length_cons,treeSize]
      omega

/-- All four recursive calls potentially present in the actual sameShape
source are charged, even when Boolean short-circuiting skips some of them. -/
def sameShapeCalls : Tree → Tree → Nat
  | .node a b, .node c d => 1 + sameShapeCalls a c + sameShapeCalls b d + sameShapeCalls a d + sameShapeCalls b c
  | _, _ => 1

theorem sameShapeCalls_bound (T S : Tree) : sameShapeCalls T S ≤ treeSize T * treeSize S := by
  induction T generalizing S with
  | leaf x =>
    cases S with
    | leaf y => simp [sameShapeCalls,treeSize]
    | node c d => simp [sameShapeCalls,treeSize]; omega
  | node a b ha hb =>
    cases S with
    | leaf x => simp [sameShapeCalls,treeSize]; omega
    | node c d =>
      have hac := ha c
      have had := ha d
      have hbc := hb c
      have hbd := hb d
      simp only [sameShapeCalls,treeSize,Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
      omega

/-- Conservative count of tree-node visits made by minimalVertices and its
rootedSpan calls. At an internal node the actual program recurses into at
most one minimal child; this envelope charges both, so it remains an upper
bound without knowing the selected set. -/
def minimalVisits : Tree → Nat
  | .leaf _ => 1
  | .node l r => 1 + treeSize l + treeSize r + minimalVisits l + minimalVisits r

theorem minimalVisits_bound (S : Tree) : minimalVisits S ≤ treeSize S * treeSize S := by
  induction S with
  | leaf x => simp [minimalVisits,treeSize]
  | node l r hl hr =>
    simp only [minimalVisits,treeSize,Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
    omega

end Universal233.DepthOne
