import Rule4MetadataV3

namespace SourcePendantValuesV3
open RMAF Universal233 Universal233.HardParent
open Universal233.Rule5PrefixLocalWork Universal233.Rule5PendantLocalWork

theorem prefixContains_value (x : Nat) (xs : List Nat) : (containsMeter x xs).value=xs.contains x := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [containsMeter,List.contains_cons]
    split <;> rename_i he
    · simp only [he,Bool.true_or]
    · simp only [he,Bool.false_or,ih]

theorem vertices_value (T : Tree) : (verticesMeter T).value=HardParent.vertices T := by
  induction T with
  | leaf x => rfl
  | node l r il ir => simp only [verticesMeter,HardParent.vertices,il,ir]

theorem span_value (D : List Nat) (T : Tree) : (spanMeter D T).value=rootedSpan D T := by
  induction T with
  | leaf x => simp only [spanMeter,rootedSpan,prefixContains_value]
  | node l r il ir =>
    simp only [spanMeter,rootedSpan,il,ir]
    split <;> rfl

theorem minimal_value (D : List Nat) (T : Tree) : (minimalMeter D T).value=minimalVertices D T := by
  induction T with
  | leaf x => simp only [minimalMeter,minimalVertices,prefixContains_value]
  | node l r il ir =>
    simp only [minimalMeter,minimalVertices,span_value,il,ir]
    split <;> first | rfl | (split <;> rfl)

theorem addressEq_value (p q : Vertex) : (eqAddressMeter p q).value=(p==q) := by
  induction p generalizing q with
  | nil => cases q <;> rfl
  | cons x xs ih =>
    cases q with
    | nil => rfl
    | cons y ys =>
      simp only [eqAddressMeter,List.cons_beq_cons]
      split <;> rename_i he
      · simp only [he,Bool.true_and,ih]
      · simp only [he,Bool.false_and]

theorem addressContains_value (p : Vertex) (qs : List Vertex) :
    (containsAddressMeter p qs).value=qs.contains p := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [containsAddressMeter,List.contains_cons,addressEq_value]
    split <;> rename_i he
    · simp only [he,Bool.true_or]
    · simp only [he,Bool.false_or,ih]

theorem dropLast_value (p : Vertex) : (dropLastMeter p).value=p.dropLast := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys => simp only [dropLastMeter,List.dropLast,ih]

theorem cutGuard_value (T : Tree) (a b : Nat) (v : Vertex) :
    (cutGuardMeter T a b v).value=
      (!v.isEmpty && (minimalVertices [a,b] T).contains v.dropLast &&
        !(minimalVertices [a,b] T).contains v) := by
  cases v with
  | nil => rfl
  | cons x xs =>
    simp only [cutGuardMeter,List.isEmpty_cons,Bool.false_eq_true,↓reduceIte,
      dropLast_value,minimal_value,addressContains_value,Bool.not_false,Bool.true_and]
    split <;> rename_i he
    · simp only [he,Bool.true_and]
    · simp only [he,Bool.false_and]

theorem cutFilter_value (T : Tree) (a b : Nat) (vs : List Vertex) :
    (cutFilterMeter T a b vs).value=vs.filter
      (fun v=>!v.isEmpty && (minimalVertices [a,b] T).contains v.dropLast &&
        !(minimalVertices [a,b] T).contains v) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [cutFilterMeter,List.filter_cons,cutGuard_value,ih]

theorem cuts_value (T : Tree) (a b : Nat) :
    (cutsMeter T a b).value=HardParent.pendantOriginal T a b := by
  simp only [cutsMeter,HardParent.pendantOriginal,vertices_value,cutFilter_value]

end SourcePendantValuesV3
