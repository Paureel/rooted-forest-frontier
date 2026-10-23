import StateSoundness
import OriginalGraph

namespace AllGoodDP
open RMAF

def shade : Tree → (Vertex → Nat) → Paint
  | .leaf x, f => .leaf x (f [])
  | .node l r, f => .node (f [])
      (shade l (fun v => f (false :: v))) (shade r (fun v => f (true :: v)))

theorem shade_root (t : Tree) (f : Vertex → Nat) : root (shade t f) = f [] := by
  cases t <;> rfl

def changeEdges : Paint → List Vertex
  | .leaf _ _ => []
  | .node c l r =>
    prependSide false ((if c == root l then [] else [[]]) ++ changeEdges l) ++
    prependSide true ((if c == root r then [] else [[]]) ++ changeEdges r)

theorem changeEdges_length (p : Paint) : (changeEdges p).length = changes p := by
  induction p with
  | leaf x c => rfl
  | node c l r hl hr =>
    cases hcl : c == root l <;> cases hcr : c == root r <;>
      simp [changeEdges,changes,prependSide,delta,hcl,hcr,hl,hr] <;> omega

theorem changeEdges_nonroot (p : Paint) : [] ∉ changeEdges p := by
  cases p <;> simp [changeEdges,prependSide]

theorem prepend_nodup (b : Bool) (F : List Vertex) (hn : F.Nodup) :
    (prependSide b F).Nodup := by
  induction F with
  | nil => simp [prependSide]
  | cons a F ih =>
    have hp := List.nodup_cons.1 hn
    simp only [prependSide,List.map_cons,List.nodup_cons]
    refine ⟨?_,ih hp.2⟩
    intro hm
    obtain ⟨v,hv,he⟩ := List.mem_map.1 hm
    exact hp.1 ((List.cons.inj he).2 ▸ hv)

theorem changeEdges_nodup (p : Paint) : (changeEdges p).Nodup := by
  induction p with
  | leaf x c => simp [changeEdges]
  | node c l r hl hr =>
    apply List.nodup_append.2
    refine ⟨?_,?_,?_⟩
    · apply prepend_nodup
      cases h : c == root l <;> simp [h,changeEdges_nonroot,hl]
    · apply prepend_nodup
      cases h : c == root r <;> simp [h,changeEdges_nonroot,hr]
    · intro a ha b hb he
      obtain ⟨v,hv,rfl⟩ := List.mem_map.1 ha
      obtain ⟨w,hw,rfl⟩ := List.mem_map.1 hb
      simp at he

theorem shade_valid (t : Tree) (f : Vertex → Nat) (cs : List Nat) (own : Nat → Nat)
    (hc : ∀ v, Universal233.CoreGraph.Valid t v → f v ∈ cs)
    (hl : ∀ v x, Universal233.CoreGraph.LeafAt t v x → f v = own x) : Valid cs own t (shade t f) := by
  induction t generalizing f with
  | leaf x =>
    have he := hl [] x rfl
    simp only [shade,he]
    exact Valid.leaf x (he ▸ hc [] ⟨_,rfl⟩)
  | node l r ihl ihr =>
    apply Valid.node (f []) (hc [] ⟨_,rfl⟩)
    · apply ihl
      · intro v hv; exact hc (false :: v) (by simpa [Universal233.CoreGraph.Valid,Universal233.CoreGraph.subtree] using hv)
      · intro v x hx; exact hl (false :: v) x (by simpa [Universal233.CoreGraph.LeafAt,Universal233.CoreGraph.subtree] using hx)
    · apply ihr
      · intro v hv; exact hc (true :: v) (by simpa [Universal233.CoreGraph.Valid,Universal233.CoreGraph.subtree] using hv)
      · intro v x hx; exact hl (true :: v) x (by simpa [Universal233.CoreGraph.LeafAt,Universal233.CoreGraph.subtree] using hx)

theorem changed_edge_spec (t : Tree) (f : Vertex → Nat) (e : Vertex)
    (he : e ∈ changeEdges (shade t f)) :
    ∃ v b, e = v ++ [b] ∧ Universal233.CoreGraph.Valid t v ∧ Universal233.CoreGraph.Valid t e ∧ f v ≠ f e := by
  induction t generalizing f e with
  | leaf x => simp [shade,changeEdges] at he
  | node l r ihl ihr =>
    have hm : e ∈ prependSide false
        ((if f [] == f [false] then [] else [[]]) ++ changeEdges (shade l (fun v => f (false :: v)))) ∨
      e ∈ prependSide true
        ((if f [] == f [true] then [] else [[]]) ++ changeEdges (shade r (fun v => f (true :: v)))) := by
      simpa only [shade,changeEdges,shade_root,List.mem_append] using he
    rcases hm with hm | hm
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.1 hm
      rcases List.mem_append.1 ha with ha | ha
      · have hne : f [] ≠ f [false] := by
          intro hh
          simp [hh] at ha
        have hea : a = [] := by simpa [hne] using ha
        subst a
        exact ⟨[],false,rfl,⟨_,rfl⟩,⟨_,rfl⟩,hne⟩
      · obtain ⟨v,b,hvb,hv,he,hf⟩ := ihl _ _ ha
        refine ⟨false :: v,b,by simp [hvb],?_,?_,hf⟩
        · simpa [Universal233.CoreGraph.Valid,Universal233.CoreGraph.subtree] using hv
        · simpa [Universal233.CoreGraph.Valid,Universal233.CoreGraph.subtree] using he
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.1 hm
      rcases List.mem_append.1 ha with ha | ha
      · have hne : f [] ≠ f [true] := by
          intro hh
          simp [hh] at ha
        have hea : a = [] := by simpa [hne] using ha
        subst a
        exact ⟨[],true,rfl,⟨_,rfl⟩,⟨_,rfl⟩,hne⟩
      · obtain ⟨v,b,hvb,hv,he,hf⟩ := ihr _ _ ha
        refine ⟨true :: v,b,by simp [hvb],?_,?_,hf⟩
        · simpa [Universal233.CoreGraph.Valid,Universal233.CoreGraph.subtree] using hv
        · simpa [Universal233.CoreGraph.Valid,Universal233.CoreGraph.subtree] using he

theorem uncut_adj (t : Tree) (cuts : List Vertex) (v e : Vertex) (b : Bool)
    (he : e = v ++ [b]) (hv : Universal233.CoreGraph.Valid t v) (hev : Universal233.CoreGraph.Valid t e) (hn : e ∉ cuts) :
    Universal233.CutRealization.ResidualAdj t cuts v e := by
  refine ⟨⟨hv,hev,Or.inl ⟨b,he⟩⟩,?_⟩
  intro p hp
  constructor
  · rintro ⟨_,hep⟩
    exact hn (hep ▸ hp)
  · rintro ⟨hep,hvp⟩
    have hl := congrArg List.length he
    have hd := congrArg List.length hep
    have hu := congrArg List.length hvp
    simp only [List.length_append,List.length_singleton,List.length_dropLast] at *
    omega

theorem shade_cut_bound (t : Tree) (cuts : List Vertex) (f : Vertex → Nat)
    (hc : ∀ v e, Universal233.CutRealization.ResidualAdj t cuts v e → f v = f e) :
    changes (shade t f) ≤ cuts.length := by
  rw [←changeEdges_length]
  apply List.Nodup.length_le_of_subset (changeEdges_nodup _)
  intro e he
  obtain ⟨v,b,hvb,hv,hev,hf⟩ := changed_edge_spec t f e he
  by_cases hn : e ∈ cuts
  · exact hn
  · exact False.elim (hf (hc v e (uncut_adj t cuts v e b hvb hv hev hn)))

end AllGoodDP
