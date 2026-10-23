import GraphRegion

/-! One-shot independent prefix-route proof. No executable-connectivity proof
is imported. General equality with RMAF.minimalVertices is prose-derived in
DERIVATION.md; this file proves exactly the generic prefix-hull graph step. -/

namespace PrefixRoute
open PureBridge BridgeReview

/-- Terminals below r generate every intervening address, with no vertices
strictly above r. This is the address-prefix characterization being tested. -/
def Hull (r : Address) (terminal : Address → Prop) (v : Address) : Prop :=
  r.IsPrefix v ∧ ∃ p, terminal p ∧ v.IsPrefix p

 theorem adjacent_symmetric {u v : Address} (h : Adj u v) : Adj v u := by
  exact h.elim Or.inr Or.inl

 theorem concatenate {P : Address → Prop} {x y z : Address}
    (left : Walk P x y) (right : Walk P y z) : Walk P x z := by
  induction right with
  | refl _ => exact left
  | step w hadj hz ih => exact Walk.step ih hadj hz

 theorem reverse_walk {P : Address → Prop} {x y : Address}
    (w : Walk P x y) : Walk P y x := by
  induction w with
  | refl hx => exact Walk.refl hx
  | @step y z w hadj hz ih =>
    exact concatenate (Walk.step (Walk.refl hz) (adjacent_symmetric hadj) w.finish) ih

 theorem prefix_path (P : Address → Prop) (a : Address) (tail : Address)
    (inside : ∀ q, a.IsPrefix q → q.IsPrefix (a ++ tail) → P q) :
    Walk P a (a ++ tail) := by
  induction tail generalizing a with
  | nil =>
    simpa using Walk.refl (inside a (List.prefix_refl a) (by simp))
  | cons b bs ih =>
    have hstart : P a := inside a (List.prefix_refl a) (List.prefix_append a (b :: bs))
    have hnext : P (a ++ [b]) := inside (a ++ [b]) (List.prefix_append a [b]) (by
      exact ⟨bs, by simp⟩)
    have hrest : Walk P (a ++ [b]) ((a ++ [b]) ++ bs) := ih (a ++ [b]) (by
      intro q haq hq
      apply inside q ((List.prefix_append a [b]).trans haq)
      simpa using hq)
    have first : Walk P a (a ++ [b]) :=
      Walk.step (Walk.refl hstart) (Or.inl ⟨b, rfl⟩) hnext
    simpa using concatenate first hrest

 theorem hull_root_to_member {r : Address} {terminal : Address → Prop}
    {v : Address} (hv : Hull r terminal v) : Walk (Hull r terminal) r v := by
  rcases hv with ⟨⟨tail, htail⟩, p, hp, hvp⟩
  have hwalk := prefix_path (Hull r terminal) r tail (by
    intro q hrq hq
    exact ⟨hrq, p, hp, hq.trans (by simpa [htail] using hvp)⟩)
  simpa [htail] using hwalk

 theorem hull_connected {r : Address} {terminal : Address → Prop}
    {u v : Address} (hu : Hull r terminal u) (hv : Hull r terminal v) :
    Walk (Hull r terminal) u v := by
  exact concatenate (reverse_walk (hull_root_to_member hu)) (hull_root_to_member hv)

 theorem map_membership {P Q : Address → Prop} {u v : Address}
    (equivalent : ∀ x, P x ↔ Q x) (w : Walk P u v) : Walk Q u v := by
  induction w with
  | refl hx => exact Walk.refl ((equivalent _).mp hx)
  | step w hadj hz ih => exact Walk.step ih hadj ((equivalent _).mp hz)

/-- This packaging has exactly the supplied finite list. Its premise is the
prefix-hull equality, not graph connectedness or an extraction correctness axiom. -/
def package (first : Address) (rest : List Address) (r : Address)
    (terminal : Address → Prop)
    (equality : ∀ x, x ∈ first :: rest ↔ Hull r terminal x) : ConnectedSupport where
  first := first
  rest := rest
  connected := by
    intro u hu v hv
    exact map_membership (fun x => (equality x).symm)
      (hull_connected ((equality u).mp hu) ((equality v).mp hv))

 theorem package_exact_membership (first : Address) (rest : List Address)
    (r : Address) (terminal : Address → Prop)
    (equality : ∀ x, x ∈ first :: rest ↔ Hull r terminal x) (x : Address) :
    (package first rest r terminal equality).toRootedRegion.member x ↔ x ∈ first :: rest := by
  rfl

 theorem package_consumer (a b : ConnectedSupport)
    (depth : b.root.length ≤ a.root.length)
    (overlap : ∃ z, z ∈ a.first :: a.rest ∧ z ∈ b.first :: b.rest) :
    a.root ∈ b.first :: b.rest := by
  exact ConnectedSupport.deepest_graph_root_in_neighbor a b depth overlap

#print axioms hull_connected
#print axioms package
#print axioms package_exact_membership
#print axioms package_consumer
end PrefixRoute
