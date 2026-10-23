import FamilyModel

namespace TripleDP.Family

noncomputable def trimOpen (t : BTree α) (openRegion : Option Support) : Option Support := by
  classical
  exact match openRegion with
    | none => none
    | some R => if HasLeaf t R then some (OpenHull t R) else none

theorem trimOpen_none (t : BTree α) : trimOpen t none = none := rfl

theorem trimOpen_live (t : BTree α) (R : Support) (h : HasLeaf t R) :
    trimOpen t (some R) = some (OpenHull t R) := by
  classical
  simp [trimOpen, h]

theorem trimOpen_empty (t : BTree α) (R : Support) (h : ¬ HasLeaf t R) :
    trimOpen t (some R) = none := by
  classical
  simp [trimOpen, h]

theorem trimOpen_some (t : BTree α) (old : Option Support) (R : Support)
    (h : trimOpen t old = some R) :
    ∃ Q, old = some Q ∧ HasLeaf t Q ∧ R = OpenHull t Q := by
  classical
  cases old with
  | none => simp [trimOpen] at h
  | some Q =>
      by_cases hl : HasLeaf t Q
      · have he : OpenHull t Q = R := Option.some.inj (by simpa [trimOpen, hl] using h)
        exact ⟨Q, rfl, hl, he.symm⟩
      · simp [trimOpen, hl] at h

theorem trimOpen_labels (t : BTree α) (old : Option Support)
    (hconvex : ∀ R, old = some R → PathConvex R)
    (hroot : ∀ R, old = some R → R []) (v : Address) (hv : Leaf t v) :
    (∃ R, trimOpen t old = some R ∧ R v) ↔ ∃ R, old = some R ∧ R v := by
  constructor
  · rintro ⟨R, hR, hRv⟩
    rcases trimOpen_some t old R hR with ⟨Q, hQ, _, rfl⟩
    exact ⟨Q, hQ, openHull_subset t Q (hconvex Q hQ) (hroot Q hQ) v hRv⟩
  · rintro ⟨R, hR, hRv⟩
    refine ⟨OpenHull t R, ?_, hull_contains (Or.inl ⟨hv, hRv⟩)⟩
    rw [hR]
    exact trimOpen_live t R ⟨v, hv, hRv⟩

/-- Normalize all closed supports; retain and trim only a leaf-bearing open
support. The number k of charged closed regions does not change. -/
noncomputable def normalize (F : RawFamily t k) : RawFamily t k where
  closed := fun i => ClosedHull t (F.closed i)
  openRegion := trimOpen t F.openRegion
  closed_convex := fun i => hull_pathConvex _
  closed_inside := by
    intro i v hv
    exact F.closed_inside i v (closedHull_subset t (F.closed i) (F.closed_convex i) v hv)
  closed_live := by
    intro i
    rcases F.closed_live i with ⟨v, hv⟩
    exact ⟨v, hv.1, hull_contains hv⟩
  closed_root := by
    intro i hi
    exact F.closed_root i (closedHull_subset t (F.closed i) (F.closed_convex i) [] hi)
  closed_disjoint := by
    intro i j v hi hj
    exact F.closed_disjoint i j v
      (closedHull_subset t (F.closed i) (F.closed_convex i) v hi)
      (closedHull_subset t (F.closed j) (F.closed_convex j) v hj)
  open_convex := by
    intro R hR
    rcases trimOpen_some t F.openRegion R hR with ⟨Q, _, _, rfl⟩
    exact hull_pathConvex _
  open_inside := by
    intro R hR v hv
    rcases trimOpen_some t F.openRegion R hR with ⟨Q, hQ, _, rfl⟩
    exact F.open_inside Q hQ v
      (openHull_subset t Q (F.open_convex Q hQ) (F.open_root Q hQ) v hv)
  open_root := by
    intro R hR
    rcases trimOpen_some t F.openRegion R hR with ⟨Q, _, _, rfl⟩
    exact hull_contains (Or.inr rfl)
  open_disjoint := by
    intro R hR i v hRv hi
    rcases trimOpen_some t F.openRegion R hR with ⟨Q, hQ, _, rfl⟩
    exact F.open_disjoint Q hQ i v
      (openHull_subset t Q (F.open_convex Q hQ) (F.open_root Q hQ) v hRv)
      (closedHull_subset t (F.closed i) (F.closed_convex i) v hi)
  covers := by
    intro v hv
    rcases F.covers v hv with ⟨i, hi⟩ | ho
    · exact Or.inl ⟨i, hull_contains ⟨hv, hi⟩⟩
    · exact Or.inr ((trimOpen_labels t F.openRegion F.open_convex F.open_root v hv).mpr ho)

theorem normalize_retained (F : RawFamily t k) : Retained (normalize F) := by
  intro R hR
  rcases trimOpen_some t F.openRegion R hR with ⟨Q, hQ, hLive, rfl⟩
  rcases hLive with ⟨v, hv⟩
  exact ⟨v, hv.1, hull_contains (Or.inl hv)⟩

theorem normalize_closed_labels (F : RawFamily t k) (i : Fin k) :
    LeafSet t ((normalize F).closed i) = LeafSet t (F.closed i) :=
  closedHull_labels t (F.closed i) (F.closed_convex i)

theorem normalize_open_labels (F : RawFamily t k) (v : Address) (hv : Leaf t v) :
    (∃ R, (normalize F).openRegion = some R ∧ R v) ↔
    ∃ R, F.openRegion = some R ∧ R v :=
  trimOpen_labels t F.openRegion F.open_convex F.open_root v hv

theorem normalize_closed_cost (F : RawFamily t k) :
    closedCost (normalize F) = closedCost F := rfl

def OpenHasLeaf (F : RawFamily t k) : Prop :=
  ∃ R, F.openRegion = some R ∧ HasLeaf t R

theorem normalize_open_hasLeaf (F : RawFamily t k) :
    OpenHasLeaf (normalize F) ↔ OpenHasLeaf F := by
  constructor
  · rintro ⟨R, hR, v, hv⟩
    rcases (normalize_open_labels F v hv.1).mp ⟨R, hR, hv.2⟩ with ⟨Q, hQ, hQv⟩
    exact ⟨Q, hQ, v, hv.1, hQv⟩
  · rintro ⟨R, hR, v, hv⟩
    rcases (normalize_open_labels F v hv.1).mpr ⟨R, hR, hv.2⟩ with ⟨Q, hQ, hQv⟩
    exact ⟨Q, hQ, v, hv.1, hQv⟩

noncomputable def labelledBlocks (F : RawFamily t k) : Nat := by
  classical
  exact k + if OpenHasLeaf F then 1 else 0

theorem normalize_labelled_blocks (F : RawFamily t k) :
    labelledBlocks (normalize F) = labelledBlocks F := by
  classical
  simp only [labelledBlocks, normalize_open_hasLeaf F]

/-- Any predicate of a closed block's leaf set is preserved, including a
color or bad-triple admissibility predicate supplied by a later interface. -/
theorem normalize_closed_property (F : RawFamily t k) (P : Support → Prop) (i : Fin k) :
    P (LeafSet t ((normalize F).closed i)) ↔ P (LeafSet t (F.closed i)) := by
  rw [normalize_closed_labels F i]

theorem normalized_closed_is_hull (F : RawFamily t k) (i : Fin k) :
    (normalize F).closed i = ClosedHull t ((normalize F).closed i) := by
  change ClosedHull t (F.closed i) = Hull (LeafSet t (ClosedHull t (F.closed i)))
  rw [closedHull_labels t (F.closed i) (F.closed_convex i)]
  rfl

theorem normalized_open_is_hull (F : RawFamily t k) (R : Support)
    (hR : (normalize F).openRegion = some R) : R = OpenHull t R := by
  rcases trimOpen_some t F.openRegion R hR with ⟨Q, hQ, _, rfl⟩
  change OpenHull t Q = Hull (fun v => LeafSet t (OpenHull t Q) v ∨ v = [])
  rw [openHull_labels t Q (F.open_convex Q hQ) (F.open_root Q hQ)]
  rfl

theorem normalize_open_property (F : RawFamily t k) (P : Support → Prop)
    (hP : ∀ Q, F.openRegion = some Q → HasLeaf t Q → P (LeafSet t Q)) :
    ∀ R, (normalize F).openRegion = some R → P (LeafSet t R) := by
  intro R hR
  rcases trimOpen_some t F.openRegion R hR with ⟨Q, hQ, hLive, rfl⟩
  rw [openHull_labels t Q (F.open_convex Q hQ) (F.open_root Q hQ)]
  exact hP Q hQ hLive

/-- A universal labelled-family normal-form theorem in this finite address
model. The returned RawFamily carries all coverage/disjointness/convexity
proofs. No claim about four-transition completeness is made here. -/
theorem normalization_theorem (T : LabelledTree α) (F : RawFamily T.tree k) :
    ∃ G : RawFamily T.tree k,
      Retained G ∧ closedCost G = closedCost F ∧ labelledBlocks G = labelledBlocks F ∧
      (∀ i, LeafSet T.tree (G.closed i) = LeafSet T.tree (F.closed i)) ∧
      (∀ v, Leaf T.tree v →
        ((∃ R, G.openRegion = some R ∧ R v) ↔ ∃ R, F.openRegion = some R ∧ R v)) ∧
      (∀ i, G.closed i = ClosedHull T.tree (G.closed i)) ∧
      (∀ R, G.openRegion = some R → R = OpenHull T.tree R) := by
  exact ⟨normalize F, normalize_retained F, normalize_closed_cost F,
    normalize_labelled_blocks F, normalize_closed_labels F, normalize_open_labels F,
    normalized_closed_is_hull F, normalized_open_is_hull F⟩

#print axioms trimOpen_live
#print axioms trimOpen_empty
#print axioms trimOpen_some
#print axioms trimOpen_labels
#print axioms normalize
#print axioms normalize_retained
#print axioms normalize_closed_labels
#print axioms normalize_open_labels
#print axioms normalize_closed_cost
#print axioms normalize_open_hasLeaf
#print axioms normalize_labelled_blocks
#print axioms normalize_closed_property
#print axioms normalized_closed_is_hull
#print axioms normalized_open_is_hull
#print axioms normalize_open_property
#print axioms normalization_theorem
end TripleDP.Family
