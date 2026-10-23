-- Own original-address facts and frontier exclusion.
import Prefix13
open RMAF Universal233 VertexGeometry OwnHigh
namespace SourceBoundary
theorem subtree_compose (T : Tree) (p q : List Bool) :
    CoreGraph.subtree T (p++q) = (CoreGraph.subtree T p).bind (fun U => CoreGraph.subtree U q) := by
  induction p generalizing T with
  | nil => rfl
  | cons s p ih =>
    cases T with
    | leaf x => simp [CoreGraph.subtree]
    | node L R =>
      cases s
      · simpa [CoreGraph.subtree] using ih L
      · simpa [CoreGraph.subtree] using ih R
theorem subtree_labels_eq (T : Tree) (p : List Bool) :
    HardParent.subtreeLabels T p = match CoreGraph.subtree T p with
      | none => [] | some U => leaves U := by
  induction p generalizing T with
  | nil => rfl
  | cons s p ih =>
    cases T with
    | leaf x => simp [HardParent.subtreeLabels,CoreGraph.subtree]
    | node L R =>
      cases s
      · simpa [HardParent.subtreeLabels,CoreGraph.subtree] using ih L
      · simpa [HardParent.subtreeLabels,CoreGraph.subtree] using ih R
theorem label_has_leaf (T : Tree) (x : Nat) (hx : x ∈ leaves T) :
    ∃ p, CoreGraph.subtree T p = some (.leaf x) := by
  induction T with
  | leaf y =>
    simp only [leaves,List.mem_singleton] at hx
    subst x
    exact ⟨[],rfl⟩
  | node L R ihL ihR =>
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨p,hp⟩ := ihL hx
      exact ⟨false::p,by simpa [CoreGraph.subtree] using hp⟩
    · obtain ⟨p,hp⟩ := ihR hx
      exact ⟨true::p,by simpa [CoreGraph.subtree] using hp⟩
theorem selected_leaf_iff (D : List Nat) (T : Tree) (p : List Bool) :
    selectedLeaves D T p ↔ ∃ x, x ∈ D ∧ CoreGraph.subtree T p = some (.leaf x) := by
  induction p generalizing T with
  | nil => cases T <;> simp [selectedLeaves,Join,CoreGraph.subtree]
  | cons s p ih =>
    cases T with
    | leaf x => simp [selectedLeaves,Join,CoreGraph.subtree]
    | node L R =>
      cases s
      · simpa [selectedLeaves,Join,CoreGraph.subtree] using ih L
      · simpa [selectedLeaves,Join,CoreGraph.subtree] using ih R
theorem label_below_has_leaf (T : Tree) (v : List Bool) (x : Nat)
    (hx : x ∈ HardParent.subtreeLabels T v) :
    ∃ p, v <+: p ∧ CoreGraph.subtree T p = some (.leaf x) := by
  rw [subtree_labels_eq] at hx
  cases hv : CoreGraph.subtree T v with
  | none => simp [hv] at hx
  | some V =>
    have hxV : x ∈ leaves V := by simpa [hv] using hx
    obtain ⟨p,hp⟩ := label_has_leaf V x hxV
    exact ⟨v++p,List.prefix_append v p,by simpa [subtree_compose,hv] using hp⟩
theorem leaf_below_label (T : Tree) (v p : List Bool) (x : Nat)
    (hv : v <+: p) (hp : CoreGraph.subtree T p = some (.leaf x)) :
    x ∈ HardParent.subtreeLabels T v := by
  obtain ⟨tail,rfl⟩ := hv
  rw [subtree_compose] at hp
  cases hV : CoreGraph.subtree T v with
  | none => simp [hV] at hp
  | some V =>
    have hleaf : CoreGraph.subtree V tail = some (.leaf x) := by simpa [hV] using hp
    have hx := subtree_labels_subset V (.leaf x) tail hleaf x (by simp [leaves])
    simpa [subtree_labels_eq,hV] using hx
theorem leaf_address_unique (T : Tree) (x : Nat) (p q : List Bool)
    (hn : (leaves T).Nodup) (hp : CoreGraph.subtree T p = some (.leaf x))
    (hq : CoreGraph.subtree T q = some (.leaf x)) : p=q := by
  induction T generalizing p q with
  | leaf y => cases p <;> cases q <;> simp [CoreGraph.subtree] at *
  | node L R ihL ihR =>
    have hh := List.nodup_append.mp (show (leaves L ++ leaves R).Nodup from hn)
    cases p with
    | nil => simp [CoreGraph.subtree] at hp
    | cons s p =>
      cases q with
      | nil => simp [CoreGraph.subtree] at hq
      | cons t q =>
        cases s <;> cases t
        · have hpL : CoreGraph.subtree L p = some (.leaf x) := by simpa [CoreGraph.subtree] using hp
          have hqL : CoreGraph.subtree L q = some (.leaf x) := by simpa [CoreGraph.subtree] using hq
          exact congrArg (List.cons false) (ihL p q hh.1 hpL hqL)
        · have hpL : CoreGraph.subtree L p = some (.leaf x) := by simpa [CoreGraph.subtree] using hp
          have hqR : CoreGraph.subtree R q = some (.leaf x) := by simpa [CoreGraph.subtree] using hq
          have hL := subtree_labels_subset L (.leaf x) p hpL x (by simp [leaves])
          have hR := subtree_labels_subset R (.leaf x) q hqR x (by simp [leaves])
          exact False.elim (hh.2.2 x hL x hR rfl)
        · have hpR : CoreGraph.subtree R p = some (.leaf x) := by simpa [CoreGraph.subtree] using hp
          have hqL : CoreGraph.subtree L q = some (.leaf x) := by simpa [CoreGraph.subtree] using hq
          have hL := subtree_labels_subset L (.leaf x) q hqL x (by simp [leaves])
          have hR := subtree_labels_subset R (.leaf x) p hpR x (by simp [leaves])
          exact False.elim (hh.2.2 x hL x hR rfl)
        · have hpR : CoreGraph.subtree R p = some (.leaf x) := by simpa [CoreGraph.subtree] using hp
          have hqR : CoreGraph.subtree R q = some (.leaf x) := by simpa [CoreGraph.subtree] using hq
          exact congrArg (List.cons true) (ihR p q hh.2.1 hpR hqR)
theorem leaf_cluster_prefix (T V : Tree) (r p : List Bool) (x : Nat)
    (hn : (leaves T).Nodup) (hr : CoreGraph.subtree T r = some V)
    (hx : x ∈ leaves V) (hp : CoreGraph.subtree T p = some (.leaf x)) : r <+: p := by
  obtain ⟨q,hq⟩ := label_has_leaf V x hx
  have hp' : CoreGraph.subtree T (r++q) = some (.leaf x) := by
    simpa [subtree_compose,hr] using hq
  have he := leaf_address_unique T x p (r++q) hn hp hp'
  rw [he]
  exact List.prefix_append r q
theorem child_parent_path (v z : List Bool) (hv : v <+: z) :
    PathAt v v.dropLast z := by
  induction v generalizing z with
  | nil => exact PathAt.endpointL [] z
  | cons s v ih =>
    obtain ⟨tail,rfl⟩ := hv
    cases v with
    | nil => exact PathAt.rightLeg s (PathAt.endpointL [] tail)
    | cons t v => exact PathAt.down s (ih ((t::v)++tail) (List.prefix_append _ _))
theorem frontier_label_absent (T : Tree) (D : List Nat) (v : List Bool)
    (hw : v.dropLast ∈ minimalVertices D T) (hv : v ∉ minimalVertices D T)
    (x : Nat) (hx : x ∈ HardParent.subtreeLabels T v) (hD : x ∈ D) : False := by
  obtain ⟨z,hvz,hz⟩ := label_below_has_leaf T v x hx
  have hsel : selectedLeaves D T z := (selected_leaf_iff D T z).mpr ⟨x,hD,hz⟩
  have hzH : Hull (selectedLeaves D T) z := ⟨z,z,hsel,hsel,PathAt.endpointL z z⟩
  have hwH := (minimalVertices_correct D T v.dropLast).mp hw
  have hvH := hull_convex (selectedLeaves D T) v v.dropLast z hwH hzH (child_parent_path v z hvz)
  exact hv ((minimalVertices_correct D T v).mpr hvH)
end SourceBoundary
