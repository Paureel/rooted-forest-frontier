-- Own source-address lifting, using only explicitly granted generic restriction facts.
import Boundary26
open RMAF Universal233 OwnHigh
namespace SourceBoundary
theorem leaf_no_cherry (x a b : Nat) : ¬ HasCherry (.leaf x) a b := by
  rintro ⟨q,hq⟩
  cases q <;> simp [CoreGraph.CherryAt, CoreGraph.subtree] at hq
theorem node_cherry_iff (L R : Tree) (a b : Nat) :
    HasCherry (.node L R) a b ↔
      ((L = .leaf a ∧ R = .leaf b) ∨ (L = .leaf b ∧ R = .leaf a)) ∨
      HasCherry L a b ∨ HasCherry R a b := by
  constructor
  · rintro ⟨q,hq⟩
    cases q with
    | nil =>
      left
      simpa [CoreGraph.CherryAt, CoreGraph.subtree] using hq
    | cons side q =>
      cases side with
      | false =>
        right; left
        exact ⟨q,by simpa [CoreGraph.CherryAt,CoreGraph.subtree] using hq⟩
      | true =>
        right; right
        exact ⟨q,by simpa [CoreGraph.CherryAt,CoreGraph.subtree] using hq⟩
  · rintro (hroot | hL | hR)
    · rcases hroot with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨[],Or.inl rfl⟩
      · exact ⟨[],Or.inr rfl⟩
    · exact hasCherry_left L R a b hL
    · exact hasCherry_right L R a b hR
theorem has_cherry_labels (T : Tree) (a b : Nat) (h : HasCherry T a b) :
    a ∈ leaves T ∧ b ∈ leaves T := by
  obtain ⟨q,hq⟩ := h
  rcases hq with hq | hq
  · exact ⟨cherry_a_mem T q a b hq,cherry_b_mem T q a b hq⟩
  · exact ⟨cherry_b_mem T q b a hq,cherry_a_mem T q b a hq⟩
theorem lift_restricted_cherry (S U : Tree) (P : List Nat) (a b : Nat)
    (hr : restrict P S = some U) (hc : HasCherry U a b) :
    ∃ v V, CoreGraph.subtree S v = some V ∧
      (restrict P V = some (.node (.leaf a) (.leaf b)) ∨
       restrict P V = some (.node (.leaf b) (.leaf a))) := by
  induction S generalizing U with
  | leaf x =>
    simp only [restrict] at hr
    split at hr
    · cases Option.some.inj hr
      exact False.elim (leaf_no_cherry x a b hc)
    · contradiction
  | node L R ihL ihR =>
    cases hL : restrict P L with
    | none =>
      cases hR : restrict P R with
      | none => simp [restrict,hL,hR] at hr
      | some UR =>
        have he : UR = U := by simpa [restrict,hL,hR] using hr
        subst U
        obtain ⟨v,V,hv,hV⟩ := ihR UR hR hc
        exact ⟨true::v,V,by simpa [CoreGraph.subtree] using hv,hV⟩
    | some UL =>
      cases hR : restrict P R with
      | none =>
        have he : UL = U := by simpa [restrict,hL,hR] using hr
        subst U
        obtain ⟨v,V,hv,hV⟩ := ihL UL hL hc
        exact ⟨false::v,V,by simpa [CoreGraph.subtree] using hv,hV⟩
      | some UR =>
        have he : Tree.node UL UR = U := by simpa [restrict,hL,hR] using hr
        subst U
        rcases (node_cherry_iff UL UR a b).mp hc with hroot | hcL | hcR
        · refine ⟨[],.node L R,rfl,?_⟩
          rcases hroot with ⟨h1,h2⟩ | ⟨h1,h2⟩
          · left; simpa [restrict,hL,hR,h1,h2]
          · right; simpa [restrict,hL,hR,h1,h2]
        · obtain ⟨v,V,hv,hV⟩ := ihL UL hL hcL
          exact ⟨false::v,V,by simpa [CoreGraph.subtree] using hv,hV⟩
        · obtain ⟨v,V,hv,hV⟩ := ihR UR hR hcR
          exact ⟨true::v,V,by simpa [CoreGraph.subtree] using hv,hV⟩
theorem selected_cluster (S U : Tree) (P : List Nat) (a b : Nat)
    (hr : restrict P S = some U) (hc : HasCherry U a b) :
    ∃ v V, CoreGraph.subtree S v = some V ∧
      ∀ x, (x ∈ leaves V ∧ x ∈ P) ↔ x = a ∨ x = b := by
  obtain ⟨v,V,hv,hV⟩ := lift_restricted_cherry S U P a b hr hc
  refine ⟨v,V,hv,?_⟩
  intro x
  rcases hV with hr | hr
  · simpa [leaves] using (RestrictionBridge.restricted_labels_exact V (.node (.leaf a) (.leaf b)) P hr (x:=x)).symm
  · simpa [leaves,or_comm] using (RestrictionBridge.restricted_labels_exact V (.node (.leaf b) (.leaf a)) P hr (x:=x)).symm
#print axioms lift_restricted_cherry
#print axioms selected_cluster
end SourceBoundary
