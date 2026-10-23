import Profile
namespace FreshClade
open RMAF
def hits (A B : List Vertex) : Bool := A.any B.contains
theorem hits_true (A B : List Vertex) : hits A B = true ↔ ∃v, v∈A ∧ v∈B := by
 simp [hits,List.any_eq_true]
theorem bool_ext {a b : Bool} (h : (a=true ↔ b=true)) : a=b := by
 cases a <;> cases b <;> simp_all
@[simp] theorem hits_nil_left (A : List Vertex) : hits [] A = false := rfl
@[simp] theorem hits_nil_right (A : List Vertex) : hits A [] = false := by simp [hits]
@[simp] theorem hits_append_left (A B C : List Vertex) : hits (A++B) C = (hits A C || hits B C) := by
 exact bool_ext (by simp [hits_true,List.mem_append,or_and_right,exists_or])
@[simp] theorem hits_append_right (A B C : List Vertex) : hits A (B++C) = (hits A B || hits A C) := by
 exact bool_ext (by simp [hits_true,List.mem_append,and_or_left,exists_or])
@[simp] theorem hits_cons_left (v : Vertex) (A B : List Vertex) :
 hits (v::A) B = (B.contains v || hits A B) := by simp [hits]
@[simp] theorem hits_cons_right (v : Vertex) (A B : List Vertex) :
 hits A (v::B) = (A.contains v || hits A B) := by
 exact bool_ext (by simp [hits_true,List.mem_cons,and_or_left,exists_or])
@[simp] theorem contains_root_prefix (s : Bool) (A : List Vertex) :
 (prependSide s A).contains [] = false := by
 apply bool_ext
 simp [prependSide]
@[simp] theorem prefix_nil (s : Bool) : prependSide s [] = [] := rfl
@[simp] theorem root_not_mem_prefix (s : Bool) (A : List Vertex) : [] ∉ prependSide s A := by
 simp [prependSide]
@[simp] theorem isEmpty_of_ne_nil {α : Type} (A : List α) (h : A≠[]) : A.isEmpty=false := by
 cases A <;> simp_all
@[simp] theorem hits_prefix_same (s : Bool) (A B : List Vertex) :
 hits (prependSide s A) (prependSide s B) = hits A B := by
 apply bool_ext
 simp only [hits_true,prependSide,List.mem_map]
 constructor
 · rintro ⟨v,⟨a,ha,rfl⟩,b,hb,he⟩
   cases List.cons.inj he |>.2
   exact ⟨a,ha,hb⟩
 · rintro ⟨a,ha,hb⟩
   exact ⟨s::a,⟨a,ha,rfl⟩,⟨a,hb,rfl⟩⟩
@[simp] theorem hits_prefix_different (s t : Bool) (h : s≠t) (A B : List Vertex) :
 hits (prependSide s A) (prependSide t B) = false := by
 cases e : hits (prependSide s A) (prependSide t B)
 · rfl
 · have ht := (hits_true _ _).mp e
   rcases ht with ⟨v,hv,hw⟩
   simp only [prependSide,List.mem_map] at hv hw
   rcases hv with ⟨a,ha,rfl⟩
   rcases hw with ⟨b,hb,he⟩
   exact False.elim (h (List.cons.inj he).1.symm)

theorem span_empty_min_empty (C : List Nat) (T : Tree)
 (h : rootedSpan C T = []) : minimalVertices C T = [] := by
 induction T with
 | leaf x => simpa [minimalVertices,rootedSpan] using h
 | node l r il ir =>
   by_cases hl : rootedSpan C l = []
   · by_cases hr : rootedSpan C r = []
     · simp [minimalVertices,hl,hr,il hl,ir hr,prependSide]
     · simp [rootedSpan,hl,hr,List.isEmpty_iff] at h
   · simp [rootedSpan,hl,List.isEmpty_iff] at h

def observe (C D : List Nat) (T : Tree) : Profile :=
 ⟨!(rootedSpan C T).isEmpty,!(rootedSpan D T).isEmpty,
  hits (minimalVertices C T) (rootedSpan D T),
  hits (rootedSpan C T) (minimalVertices D T),
  hits (minimalVertices C T) (minimalVertices D T)⟩

theorem observe_leaf (C D : List Nat) (x : Nat) :
 observe C D (.leaf x) = profile C D (.leaf x) := by
 by_cases hc : x∈C <;> by_cases hd : x∈D <;>
  simp [observe,profile,rootedSpan,minimalVertices,hc,hd,hits]

theorem observe_node (C D : List Nat) (l r : Tree) :
 observe C D (.node l r) = merge (observe C D l) (observe C D r) := by
 by_cases cl : rootedSpan C l = [] <;> by_cases cr : rootedSpan C r = [] <;>
  by_cases dl : rootedSpan D l = [] <;> by_cases dr : rootedSpan D r = []
 all_goals
  have cmL : rootedSpan C l = [] → minimalVertices C l = [] := span_empty_min_empty C l
  have cmR : rootedSpan C r = [] → minimalVertices C r = [] := span_empty_min_empty C r
  have dmL : rootedSpan D l = [] → minimalVertices D l = [] := span_empty_min_empty D l
  have dmR : rootedSpan D r = [] → minimalVertices D r = [] := span_empty_min_empty D r
  simp_all [observe,rootedSpan,minimalVertices,merge,List.isEmpty_iff,
   List.contains_append]

theorem observe_profile (C D : List Nat) (T : Tree) : observe C D T = profile C D T := by
 induction T with
 | leaf x => exact observe_leaf C D x
 | node l r il ir => rw [observe_node,profile,il,ir]
end FreshClade
