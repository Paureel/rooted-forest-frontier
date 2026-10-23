import Restriction

namespace RestrictionBridge
open RMAF

def Clear (a b : List Vertex) : Prop := ∀ v, v ∈ a → v ∈ b → False

theorem clear_iff (a b : List Vertex) : disjointVertices a b = true ↔ Clear a b := by
  simp [disjointVertices, Clear, List.all_eq_true]

theorem clear_symm (a b : List Vertex) : Clear a b ↔ Clear b a := by
  constructor <;> intro h v ha hb
  · exact h v hb ha
  · exact h v hb ha

@[simp] theorem clear_nil_left (a : List Vertex) : Clear [] a := by simp [Clear]
@[simp] theorem clear_nil_right (a : List Vertex) : Clear a [] := by simp [Clear]
@[simp] theorem clear_cons_left (v : Vertex) (a b : List Vertex) :
    Clear (v :: a) b ↔ v ∉ b ∧ Clear a b := by
  constructor
  · intro h; exact ⟨h v (by simp),fun x hx => h x (by simp [hx])⟩
  · rintro ⟨hv,ha⟩ x hx hb
    rcases List.mem_cons.1 hx with he | hm
    · subst x; exact hv hb
    · exact ha x hm hb
@[simp] theorem clear_append_left (a b c : List Vertex) :
    Clear (a ++ b) c ↔ Clear a c ∧ Clear b c := by
  constructor
  · intro h; exact ⟨fun x hx => h x (List.mem_append_left b hx),
      fun x hx => h x (List.mem_append_right a hx)⟩
  · rintro ⟨ha,hb⟩ x hx hc
    rcases List.mem_append.1 hx with hx | hx
    · exact ha x hx hc
    · exact hb x hx hc
@[simp] theorem clear_cons_right (v : Vertex) (a b : List Vertex) :
    Clear a (v :: b) ↔ v ∉ a ∧ Clear a b := by rw [clear_symm,clear_cons_left,clear_symm]
@[simp] theorem clear_append_right (a b c : List Vertex) :
    Clear a (b ++ c) ↔ Clear a b ∧ Clear a c := by
  rw [clear_symm,clear_append_left,clear_symm b a,clear_symm c a]
@[simp] theorem root_not_prepend (s : Bool) (a : List Vertex) : [] ∉ prependSide s a := by
  simp [prependSide]
@[simp] theorem clear_prepend_same (s : Bool) (a b : List Vertex) :
    Clear (prependSide s a) (prependSide s b) ↔ Clear a b := by
  simp only [Clear, prependSide, List.mem_map]
  constructor
  · intro h v ha hb
    exact h (s :: v) ⟨v,ha,rfl⟩ ⟨v,hb,rfl⟩
  · rintro h v ⟨x,hx,rfl⟩ ⟨y,hy,hyx⟩
    have hh : y = x := List.cons.inj hyx |>.2
    subst y
    exact h x hx hy
@[simp] theorem clear_prepend_other (a b : List Vertex) :
    Clear (prependSide false a) (prependSide true b) := by
  rintro v hv hw
  rcases List.mem_map.1 hv with ⟨x,hx,hxv⟩
  rcases List.mem_map.1 hw with ⟨y,hy,hyv⟩
  have := hxv.trans hyv.symm
  simp at this
@[simp] theorem clear_prepend_other' (a b : List Vertex) :
    Clear (prependSide true a) (prependSide false b) :=
  (clear_symm _ _).2 (clear_prepend_other b a)

theorem span_empty (B : List Nat) (t : Tree) :
    (rootedSpan B t).isEmpty = (restrict B t).isNone := by
  induction t with
  | leaf x => by_cases h : x ∈ B <;> simp [rootedSpan,restrict,h]
  | node l r hl hr =>
    simp only [rootedSpan, hl, hr]
    cases hbl : restrict B l <;> cases hbr : restrict B r <;>
      simp [restrict, hbl, hbr]

theorem minimal_empty (B : List Nat) (t : Tree) :
    (minimalVertices B t).isEmpty = (restrict B t).isNone := by
  induction t with
  | leaf x => by_cases h : x ∈ B <;> simp [minimalVertices,restrict,h]
  | node l r hl hr =>
    simp only [minimalVertices, span_empty]
    cases hbl : restrict B l <;> cases hbr : restrict B r <;>
      simp [restrict,hbl,hbr,prependSide,hl,hr]

theorem empty_selection (B U : List Nat) (t : Tree) (sub : B ⊆ U)
    (hu : restrict U t = none) : rootedSpan B t = [] ∧ minimalVertices B t = [] := by
  have hn : restrict B t = none := by
    have hh := restrict_nested t U B sub
    simpa [hu] using hh.symm
  have hs := span_empty B t
  have hm := minimal_empty B t
  simp only [hn,Option.isNone_none,List.isEmpty_iff] at hs hm
  exact ⟨hs,hm⟩

theorem span_root (B : List Nat) (t : Tree) :
    [] ∈ rootedSpan B t ↔ (rootedSpan B t).isEmpty = false := by
  cases t with
  | leaf x => by_cases hx : x ∈ B <;> simp [rootedSpan,hx]
  | node l r =>
    by_cases h : (rootedSpan B l).isEmpty && (rootedSpan B r).isEmpty = true <;>
      simp [rootedSpan,h]

theorem minimal_nil_of_span_nil (B : List Nat) (t : Tree) (h : rootedSpan B t = []) :
    minimalVertices B t = [] := by
  have hs := span_empty B t
  have hm := minimal_empty B t
  rw [h] at hs
  have he : (minimalVertices B t).isEmpty = true := hm.trans hs.symm
  simpa only [List.isEmpty_iff] using he

theorem unary_left_clear (l r : Tree) (B C : List Nat)
    (hb : rootedSpan B r = []) (hc : rootedSpan C r = []) :
    (Clear (rootedSpan B (.node l r)) (minimalVertices C (.node l r)) ↔
      Clear (rootedSpan B l) (minimalVertices C l)) ∧
    (Clear (minimalVertices B (.node l r)) (minimalVertices C (.node l r)) ↔
      Clear (minimalVertices B l) (minimalVertices C l)) := by
  have mb := minimal_nil_of_span_nil B r hb
  have mc := minimal_nil_of_span_nil C r hc
  cases ebl : (rootedSpan B l).isEmpty <;> cases ecl : (rootedSpan C l).isEmpty
  all_goals
    try have nb : rootedSpan B l = [] := List.isEmpty_iff.1 ebl
    try have nc : rootedSpan C l = [] := List.isEmpty_iff.1 ecl
    try have nmb := minimal_nil_of_span_nil B l nb
    try have nmc := minimal_nil_of_span_nil C l nc
    simp_all [rootedSpan,minimalVertices]

theorem unary_right_clear (l r : Tree) (B C : List Nat)
    (hb : rootedSpan B l = []) (hc : rootedSpan C l = []) :
    (Clear (rootedSpan B (.node l r)) (minimalVertices C (.node l r)) ↔
      Clear (rootedSpan B r) (minimalVertices C r)) ∧
    (Clear (minimalVertices B (.node l r)) (minimalVertices C (.node l r)) ↔
      Clear (minimalVertices B r) (minimalVertices C r)) := by
  have mb := minimal_nil_of_span_nil B l hb
  have mc := minimal_nil_of_span_nil C l hc
  cases ebr : (rootedSpan B r).isEmpty <;> cases ecr : (rootedSpan C r).isEmpty
  all_goals
    try have nb : rootedSpan B r = [] := List.isEmpty_iff.1 ebr
    try have nc : rootedSpan C r = [] := List.isEmpty_iff.1 ecr
    try have nmb := minimal_nil_of_span_nil B r nb
    try have nmc := minimal_nil_of_span_nil C r nc
    simp_all [rootedSpan,minimalVertices]

theorem node_clear_congr (l r ul ur : Tree) (B C : List Nat)
    (ebl : (rootedSpan B l).isEmpty = (rootedSpan B ul).isEmpty)
    (ebr : (rootedSpan B r).isEmpty = (rootedSpan B ur).isEmpty)
    (ecl : (rootedSpan C l).isEmpty = (rootedSpan C ul).isEmpty)
    (ecr : (rootedSpan C r).isEmpty = (rootedSpan C ur).isEmpty)
    (hlroot : Clear (rootedSpan B l) (minimalVertices C l) ↔ Clear (rootedSpan B ul) (minimalVertices C ul))
    (hrroot : Clear (rootedSpan B r) (minimalVertices C r) ↔ Clear (rootedSpan B ur) (minimalVertices C ur))
    (hlback : Clear (rootedSpan C l) (minimalVertices B l) ↔ Clear (rootedSpan C ul) (minimalVertices B ul))
    (hrback : Clear (rootedSpan C r) (minimalVertices B r) ↔ Clear (rootedSpan C ur) (minimalVertices B ur))
    (hlmin : Clear (minimalVertices B l) (minimalVertices C l) ↔ Clear (minimalVertices B ul) (minimalVertices C ul))
    (hrmin : Clear (minimalVertices B r) (minimalVertices C r) ↔ Clear (minimalVertices B ur) (minimalVertices C ur)) :
    (Clear (rootedSpan B (.node l r)) (minimalVertices C (.node l r)) ↔
      Clear (rootedSpan B (.node ul ur)) (minimalVertices C (.node ul ur))) ∧
    (Clear (minimalVertices B (.node l r)) (minimalVertices C (.node l r)) ↔
      Clear (minimalVertices B (.node ul ur)) (minimalVertices C (.node ul ur))) := by
  cases bl : (rootedSpan B ul).isEmpty <;> cases br : (rootedSpan B ur).isEmpty <;>
    cases cl : (rootedSpan C ul).isEmpty <;> cases cr : (rootedSpan C ur).isEmpty
  all_goals
    try have nb1 : rootedSpan B l = [] := List.isEmpty_iff.1 (ebl.trans bl)
    try have nb2 : rootedSpan B r = [] := List.isEmpty_iff.1 (ebr.trans br)
    try have nc1 : rootedSpan C l = [] := List.isEmpty_iff.1 (ecl.trans cl)
    try have nc2 : rootedSpan C r = [] := List.isEmpty_iff.1 (ecr.trans cr)
    try have nbu1 : rootedSpan B ul = [] := List.isEmpty_iff.1 bl
    try have nbu2 : rootedSpan B ur = [] := List.isEmpty_iff.1 br
    try have ncu1 : rootedSpan C ul = [] := List.isEmpty_iff.1 cl
    try have ncu2 : rootedSpan C ur = [] := List.isEmpty_iff.1 cr
    try have mb1 := minimal_nil_of_span_nil B l nb1
    try have mb2 := minimal_nil_of_span_nil B r nb2
    try have mc1 := minimal_nil_of_span_nil C l nc1
    try have mc2 := minimal_nil_of_span_nil C r nc2
    try have mbu1 := minimal_nil_of_span_nil B ul nbu1
    try have mbu2 := minimal_nil_of_span_nil B ur nbu2
    try have mcu1 := minimal_nil_of_span_nil C ul ncu1
    try have mcu2 := minimal_nil_of_span_nil C ur ncu2
    simp_all [rootedSpan,minimalVertices,span_root,clear_symm (minimalVertices B l),
      clear_symm (minimalVertices B r),clear_symm (minimalVertices B ul),clear_symm (minimalVertices B ur)]

theorem literal_clear_transport (t u : Tree) (U B C : List Nat)
    (hu : restrict U t = some u) (hB : B ⊆ U) (hC : C ⊆ U) :
    (Clear (rootedSpan B t) (minimalVertices C t) ↔
      Clear (rootedSpan B u) (minimalVertices C u)) ∧
    (Clear (minimalVertices B t) (minimalVertices C t) ↔
      Clear (minimalVertices B u) (minimalVertices C u)) := by
  induction t generalizing u B C with
  | leaf x =>
    by_cases hx : x ∈ U
    · have he : u = .leaf x := by simpa [restrict,hx] using hu.symm
      subst u; exact ⟨Iff.rfl,Iff.rfl⟩
    · simp [restrict,hx] at hu
  | node l r hl hr =>
    cases hul : restrict U l with
    | none =>
      have ebl := empty_selection B U l hB hul
      have ecl := empty_selection C U l hC hul
      cases hur : restrict U r with
      | none => simp [restrict,hul,hur] at hu
      | some ur =>
        have he : u = ur := by simpa [restrict,hul,hur] using hu.symm
        subst u
        have hi := hr ur B C hur hB hC
        have hh := unary_right_clear l r B C ebl.1 ecl.1
        exact ⟨hh.1.trans hi.1,hh.2.trans hi.2⟩
    | some ul =>
      cases hur : restrict U r with
      | none =>
        have ebr := empty_selection B U r hB hur
        have ecr := empty_selection C U r hC hur
        have he : u = ul := by simpa [restrict,hul,hur] using hu.symm
        subst u
        have hi := hl ul B C hul hB hC
        have hh := unary_left_clear l r B C ebr.1 ecr.1
        exact ⟨hh.1.trans hi.1,hh.2.trans hi.2⟩
      | some ur =>
        have he : u = .node ul ur := by simpa [restrict,hul,hur] using hu.symm
        subst u
        have il := hl ul B C hul hB hC
        have ir := hr ur B C hur hB hC
        have jl := hl ul C B hul hC hB
        have jr := hr ur C B hur hC hB
        apply node_clear_congr l r ul ur B C
        · simp only [span_empty, restrict_inside l ul U B hul hB]
        · simp only [span_empty, restrict_inside r ur U B hur hB]
        · simp only [span_empty, restrict_inside l ul U C hul hC]
        · simp only [span_empty, restrict_inside r ur U C hur hC]
        · exact il.1
        · exact ir.1
        · exact jl.1
        · exact jr.1
        · exact il.2
        · exact ir.2

theorem disjoint_transport (t u : Tree) (U B C : List Nat)
    (hu : restrict U t = some u) (hB : B ⊆ U) (hC : C ⊆ U) :
    disjointVertices (minimalVertices B t) (minimalVertices C t) = true ↔
    disjointVertices (minimalVertices B u) (minimalVertices C u) = true := by
  rw [clear_iff,clear_iff]
  exact (literal_clear_transport t u U B C hu hB hC).2

theorem pairwise_transport (t u : Tree) (U : List Nat) (F : List (List Nat))
    (hu : restrict U t = some u) (sub : ∀ B ∈ F, B ⊆ U) :
    pairwiseEmbeddings t F = true ↔ pairwiseEmbeddings u F = true := by
  induction F with
  | nil => simp [pairwiseEmbeddings]
  | cons B F ih =>
    simp only [pairwiseEmbeddings,Bool.and_eq_true,List.all_eq_true]
    have hsB := sub B (by simp)
    have hsF : ∀ C ∈ F, C ⊆ U := fun C hc => sub C (by simp [hc])
    have hh : (∀ C ∈ F, disjointVertices (minimalVertices B t) (minimalVertices C t) = true) ↔
        (∀ C ∈ F, disjointVertices (minimalVertices B u) (minimalVertices C u) = true) := by
      constructor <;> intro h C hc
      · exact (disjoint_transport t u U B C hu hsB (hsF C hc)).1 (h C hc)
      · exact (disjoint_transport t u U B C hu hsB (hsF C hc)).2 (h C hc)
    exact and_congr hh (ih hsF)

end RestrictionBridge
