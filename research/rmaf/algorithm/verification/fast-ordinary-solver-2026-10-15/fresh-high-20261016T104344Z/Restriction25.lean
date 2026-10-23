-- Own cherry restriction and unordered-shape transport.
import Shared23
open RMAF Universal233
namespace OwnHigh
def HasCherry (T : Tree) (a b : Nat) : Prop :=
  ∃ q, CoreGraph.CherryAt T q a b ∨ CoreGraph.CherryAt T q b a
theorem hasCherry_left (L R : Tree) (a b : Nat) (h : HasCherry L a b) :
    HasCherry (.node L R) a b := by
  obtain ⟨q,hq⟩ := h
  refine ⟨false :: q, ?_⟩
  simpa [CoreGraph.CherryAt, CoreGraph.subtree] using hq
theorem hasCherry_right (L R : Tree) (a b : Nat) (h : HasCherry R a b) :
    HasCherry (.node L R) a b := by
  obtain ⟨q,hq⟩ := h
  refine ⟨true :: q, ?_⟩
  simpa [CoreGraph.CherryAt, CoreGraph.subtree] using hq
theorem restrict_retains_cherry (T : Tree) (p : Vertex) (a b : Nat) (P : List Nat)
    (hc : CoreGraph.CherryAt T p a b) (ha : a ∈ P) (hb : b ∈ P) :
    ∃ U, restrict P T = some U ∧ HasCherry U a b := by
  induction p generalizing T with
  | nil =>
    have he : T = .node (.leaf a) (.leaf b) := by
      simpa [CoreGraph.CherryAt, CoreGraph.subtree] using hc
    subst T
    refine ⟨.node (.leaf a) (.leaf b), ?_, [], Or.inl ?_⟩
    · simp [restrict, ha, hb]
    · rfl
  | cons side p ih =>
    cases T with
    | leaf x => simp [CoreGraph.CherryAt, CoreGraph.subtree] at hc
    | node l r =>
      cases side with
      | false =>
        have hcl : CoreGraph.CherryAt l p a b := by
          simpa [CoreGraph.CherryAt, CoreGraph.subtree] using hc
        obtain ⟨U,hu,hcU⟩ := ih l hcl
        cases hr : restrict P r with
        | none => exact ⟨U, by simp [restrict, hu, hr], hcU⟩
        | some V => exact ⟨.node U V, by simp [restrict, hu, hr], hasCherry_left U V a b hcU⟩
      | true =>
        have hcr : CoreGraph.CherryAt r p a b := by
          simpa [CoreGraph.CherryAt, CoreGraph.subtree] using hc
        obtain ⟨U,hu,hcU⟩ := ih r hcr
        cases hl : restrict P l with
        | none => exact ⟨U, by simp [restrict, hu, hl], hcU⟩
        | some V => exact ⟨.node V U, by simp [restrict, hu, hl], hasCherry_right V U a b hcU⟩
theorem shape_cherry_transport (U V : Tree) (q : Vertex) (a b : Nat)
    (hc : CoreGraph.CherryAt U q a b) (hs : sameShape U V = true) : HasCherry V a b := by
  induction q generalizing U V with
  | nil =>
    have he : U = .node (.leaf a) (.leaf b) := by
      simpa [CoreGraph.CherryAt, CoreGraph.subtree] using hc
    subst U
    cases V with
    | leaf x => simp [sameShape] at hs
    | node vl vr =>
      cases vl with
      | node ll lr => simp [sameShape] at hs
      | leaf c =>
        cases vr with
        | node rl rr => simp [sameShape] at hs
        | leaf d =>
          simp only [sameShape, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hs
          rcases hs with ⟨h1,h2⟩ | ⟨h1,h2⟩
          · subst c; subst d; exact ⟨[], Or.inl rfl⟩
          · subst d; subst c; exact ⟨[], Or.inr rfl⟩
  | cons side q ih =>
    cases U with
    | leaf x => simp [CoreGraph.CherryAt, CoreGraph.subtree] at hc
    | node l r =>
      cases V with
      | leaf x => simp [sameShape] at hs
      | node vl vr =>
        simp only [sameShape, Bool.or_eq_true, Bool.and_eq_true] at hs
        cases side with
        | false =>
          have hcl : CoreGraph.CherryAt l q a b := by
            simpa [CoreGraph.CherryAt, CoreGraph.subtree] using hc
          rcases hs with ⟨hl,_⟩ | ⟨hl,_⟩
          · exact hasCherry_left vl vr a b (ih l vl hcl hl)
          · exact hasCherry_right vl vr a b (ih l vr hcl hl)
        | true =>
          have hcr : CoreGraph.CherryAt r q a b := by
            simpa [CoreGraph.CherryAt, CoreGraph.subtree] using hc
          rcases hs with ⟨_,hr⟩ | ⟨_,hr⟩
          · exact hasCherry_right vl vr a b (ih r vr hcr hr)
          · exact hasCherry_left vl vr a b (ih r vl hcr hr)
theorem shape_hasCherry_transport (U V : Tree) (a b : Nat)
    (hc : HasCherry U a b) (hs : sameShape U V = true) : HasCherry V a b := by
  obtain ⟨q,hq⟩ := hc
  rcases hq with hc | hc
  · exact shape_cherry_transport U V q a b hc hs
  · obtain ⟨q',hq'⟩ := shape_cherry_transport U V q b a hc hs
    exact ⟨q',hq'.symm⟩
theorem agreement_source_cherry (T S : Tree) (p : Vertex) (a b : Nat)
    (F : List (List Nat)) (P : List Nat) (hc : CoreGraph.CherryAt T p a b)
    (hag : agreement T S F = true) (hp : P ∈ F) (ha : a ∈ P) (hb : b ∈ P) :
    ∃ U, restrict P S = some U ∧ HasCherry U a b := by
  obtain ⟨U,hu,hcU⟩ := restrict_retains_cherry T p a b P hc ha hb
  have hres : restrictionAgrees T S P = true := by
    simp only [agreement, Bool.and_eq_true, List.all_eq_true] at hag
    exact hag.1.1.2 P hp
  cases hv : restrict P S with
  | none => simp [restrictionAgrees, hu, hv] at hres
  | some V =>
    have hs : sameShape U V = true := by simpa [restrictionAgrees, hu, hv] using hres
    exact ⟨V,rfl,shape_hasCherry_transport U V a b hcU hs⟩
#print axioms restrict_retains_cherry
#print axioms shape_cherry_transport
#print axioms agreement_source_cherry
end OwnHigh
