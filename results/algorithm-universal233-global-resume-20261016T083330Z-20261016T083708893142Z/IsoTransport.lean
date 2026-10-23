import TargetEmbedding

namespace AllGoodDP
open RMAF RestrictionBridge

theorem iso_leaves_mem {t u : Tree} (h : RootedIso t u) (x : Nat) :
    x ∈ leaves t ↔ x ∈ leaves u := by
  induction h with
  | leaf y => rfl
  | straight h1 h2 ih1 ih2 => simp [leaves,ih1,ih2]
  | swapped h1 h2 ih1 ih2 => simp [leaves,ih1,ih2,or_comm]

theorem span_nil_iff (t : Tree) (B : List Nat) :
    rootedSpan B t = [] ↔ ∀ x ∈ leaves t, x ∉ B := by
  constructor
  · intro he x hx hb
    obtain ⟨v,hv⟩ := restriction_exists t B ⟨x,hx,hb⟩
    have hh := span_empty B t
    simp [he,hv] at hh
  · intro hh
    exact (no_selection t B hh).1

theorem iso_span_empty {t u : Tree} (h : RootedIso t u) (B : List Nat) :
    (rootedSpan B t).isEmpty = (rootedSpan B u).isEmpty := by
  have hh : rootedSpan B t = [] ↔ rootedSpan B u = [] := by
    rw [span_nil_iff,span_nil_iff]
    constructor <;> intro hn x hx
    · exact hn x ((iso_leaves_mem h x).2 hx)
    · exact hn x ((iso_leaves_mem h x).1 hx)
  cases ht : (rootedSpan B t).isEmpty <;> cases hu : (rootedSpan B u).isEmpty
  · rfl
  · have he := hh.2 (List.isEmpty_iff.1 hu)
    simp [he] at ht
  · have he := hh.1 (List.isEmpty_iff.1 ht)
    simp [he] at hu
  · rfl

theorem swap_clear (l r : Tree) (B C : List Nat) :
    (Clear (rootedSpan B (.node l r)) (minimalVertices C (.node l r)) ↔
      Clear (rootedSpan B (.node r l)) (minimalVertices C (.node r l))) ∧
    (Clear (minimalVertices B (.node l r)) (minimalVertices C (.node l r)) ↔
      Clear (minimalVertices B (.node r l)) (minimalVertices C (.node r l))) := by
  cases bl : (rootedSpan B l).isEmpty <;> cases br : (rootedSpan B r).isEmpty <;>
    cases cl : (rootedSpan C l).isEmpty <;> cases cr : (rootedSpan C r).isEmpty
  all_goals
    try have nb1 : rootedSpan B l = [] := List.isEmpty_iff.1 bl
    try have nb2 : rootedSpan B r = [] := List.isEmpty_iff.1 br
    try have nc1 : rootedSpan C l = [] := List.isEmpty_iff.1 cl
    try have nc2 : rootedSpan C r = [] := List.isEmpty_iff.1 cr
    try have mb1 := minimal_nil_of_span_nil B l nb1
    try have mb2 := minimal_nil_of_span_nil B r nb2
    try have mc1 := minimal_nil_of_span_nil C l nc1
    try have mc2 := minimal_nil_of_span_nil C r nc2
    simp_all [rootedSpan,minimalVertices,and_comm,
      clear_symm (minimalVertices B l),clear_symm (minimalVertices B r)]

theorem iso_clear {t u : Tree} (h : RootedIso t u) (B C : List Nat) :
    (Clear (rootedSpan B t) (minimalVertices C t) ↔
      Clear (rootedSpan B u) (minimalVertices C u)) ∧
    (Clear (minimalVertices B t) (minimalVertices C t) ↔
      Clear (minimalVertices B u) (minimalVertices C u)) := by
  induction h generalizing B C with
  | leaf x => exact ⟨Iff.rfl,Iff.rfl⟩
  | @straight a b c d h1 h2 ih1 ih2 =>
    have il := ih1 B C
    have ir := ih2 B C
    have jl := ih1 C B
    have jr := ih2 C B
    exact node_clear_congr a b c d B C (iso_span_empty h1 B) (iso_span_empty h2 B)
      (iso_span_empty h1 C) (iso_span_empty h2 C) il.1 ir.1 jl.1 jr.1 il.2 ir.2
  | @swapped a b c d h1 h2 ih1 ih2 =>
    have il := ih1 B C
    have ir := ih2 B C
    have jl := ih1 C B
    have jr := ih2 C B
    have hh := node_clear_congr a b d c B C (iso_span_empty h1 B) (iso_span_empty h2 B)
      (iso_span_empty h1 C) (iso_span_empty h2 C) il.1 ir.1 jl.1 jr.1 il.2 ir.2
    exact ⟨hh.1.trans (swap_clear d c B C).1,hh.2.trans (swap_clear d c B C).2⟩

theorem iso_pairwise {t u : Tree} (h : RootedIso t u) (F : List (List Nat)) :
    pairwiseEmbeddings t F = true ↔ pairwiseEmbeddings u F = true := by
  rw [pairwise_iff,pairwise_iff]
  constructor <;> intro hp
  · refine List.Pairwise.imp (fun {B C} hc => ?_) hp
    exact (iso_clear h B C).2.1 hc
  · refine List.Pairwise.imp (fun {B C} hc => ?_) hp
    exact (iso_clear h B C).2.2 hc

def OptionIso : Option Tree → Option Tree → Prop
  | none,none => True
  | some t,some u => RootedIso t u
  | _,_ => False

theorem join_iso {a b c d : Option Tree} (h1 : OptionIso a c) (h2 : OptionIso b d) :
    OptionIso (join a b) (join c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [OptionIso,join]
  exact RootedIso.straight h1 h2

theorem join_swapped_iso {a b c d : Option Tree} (h1 : OptionIso a d) (h2 : OptionIso b c) :
    OptionIso (join a b) (join c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [OptionIso,join]
  exact RootedIso.swapped h1 h2

theorem iso_restrict {t u : Tree} (h : RootedIso t u) (B : List Nat) :
    OptionIso (restrict B t) (restrict B u) := by
  induction h with
  | leaf x => by_cases hx : x ∈ B <;> simp [restrict,hx,OptionIso,RootedIso.leaf]
  | straight h1 h2 ih1 ih2 => exact join_iso ih1 ih2
  | swapped h1 h2 ih1 ih2 => exact join_swapped_iso ih1 ih2

end AllGoodDP
