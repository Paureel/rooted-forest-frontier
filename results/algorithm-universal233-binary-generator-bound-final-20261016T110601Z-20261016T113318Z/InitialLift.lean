import Normalization

/-! One-shot exact initial call-site composition: ordinary Boolean checks,
original-label source partition, group colors, exact normalize, payload lift. -/
namespace Universal233.Integration
open RMAF CoreGraph CoreProgram VertexGeometry

def recolor (color : Nat → Nat) : Tree → Tree
  | .leaf x => .leaf (color x)
  | .node l r => .node (recolor color l) (recolor color r)

theorem recolor_subtree (color : Nat → Nat) (t : Tree) (v : RMAF.Vertex) :
    subtree (recolor color t) v = (subtree t v).map (recolor color) := by
  induction t generalizing v with
  | leaf x => cases v <;> rfl
  | node l r ihl ihr =>
    cases v with
    | nil => rfl
    | cons s v => cases s <;> first | exact ihl v | exact ihr v

theorem recolor_valid (color : Nat → Nat) (t : Tree) (v : RMAF.Vertex) :
    Valid (recolor color t) v ↔ Valid t v := by
  simp only [Valid,recolor_subtree]
  cases he : subtree t v <;> simp

theorem recolor_leaf (color : Nat → Nat) (t : Tree) (v : RMAF.Vertex) (y : Nat) :
    LeafAt (recolor color t) v y ↔ ∃ x, LeafAt t v x ∧ color x = y := by
  simp only [LeafAt,recolor_subtree]
  cases he : subtree t v with
  | none => simp
  | some s => cases s <;> simp [recolor]

/-- Relabeling preserves the actual graph and all support witnesses. -/
def recolorPartition (color : Nat → Nat) (t : Tree) (P : SourcePartition t) :
    SourcePartition (recolor color t) where
  owner := P.owner
  support := P.support
  actual := by intro i v hv; exact (recolor_valid color t v).2 (P.actual i v hv)
  terminal_exact := by
    intro i v y hv
    obtain ⟨x,hx,he⟩ := (recolor_leaf color t v y).1 hv
    exact P.terminal_exact i v x hx
  connected := by
    intro i a b ha hb
    exact walk_change_tree (P.connected i a b ha hb)
      (fun v hv => (recolor_valid color t v).2 (P.actual i v hv))
  disjoint := P.disjoint

theorem recolorPartition_monochromatic (color : Nat → Nat) (t : Tree)
    (P : SourcePartition t) (hm : Monochromatic P color) :
    Monochromatic (recolorPartition color t P) id := by
  intro a b x y ha hb he
  obtain ⟨va,hva,hxa⟩ := (recolor_leaf color t a x).1 ha
  obtain ⟨vb,hvb,hxb⟩ := (recolor_leaf color t b y).1 hb
  exact hxa.symm.trans ((hm _ _ _ _ hva hvb he).trans hxb)

theorem fromTree_skeleton (color : Nat → Nat) (p : RMAF.Vertex) (t : Tree) :
    skeleton (fromTree color p t) = recolor color t := by
  induction t generalizing p with
  | leaf x => rfl
  | node l r ihl ihr => simp [fromTree,skeleton,recolor,ihl,ihr]

theorem fromTree_group_leaf (color : Nat → Nat) (p : RMAF.Vertex) (t : Tree)
    (v : RMAF.Vertex) (x : Nat) (hv : LeafAt t v x) :
    GroupLeafAt (fromTree color p t) v ⟨p ++ v,[x],color x⟩ := by
  induction t generalizing p v with
  | leaf y =>
    cases v with
    | nil => have he : y = x := by simpa [LeafAt,subtree] using hv
             subst y; simp [GroupLeafAt,groupAt,fromTree]
    | cons s v => simp [LeafAt,subtree] at hv
  | node l r ihl ihr =>
    cases v with
    | nil => simp [LeafAt,subtree] at hv
    | cons s v =>
      cases s with
      | false => simpa [fromTree,GroupLeafAt,groupAt,List.append_assoc] using ihl (p ++ [false]) v hv
      | true => simpa [fromTree,GroupLeafAt,groupAt,List.append_assoc] using ihr (p ++ [true]) v hv

def retreePartition {t u : Tree} (h : t = u) (P : SourcePartition t) : SourcePartition u where
  owner := P.owner
  support := P.support
  actual := by intro i v hv; rw [←h]; exact P.actual i v hv
  terminal_exact := by intro i v x hv; rw [←h] at hv; exact P.terminal_exact i v x hv
  connected := by intro i v w hv hw; rw [←h]; exact P.connected i v w hv hw
  disjoint := P.disjoint

noncomputable def initialPartition (t : Tree) (bs : List (List Nat)) (color : Nat → Nat)
    (hp : RMAF.partitionCheck (RMAF.leaves t) bs = true)
    (he : RMAF.pairwiseEmbeddings t bs = true) : SourcePartition (skeleton (fromTree color [] t)) :=
  retreePartition (fromTree_skeleton color [] t).symm
    (recolorPartition color t (checkedSourcePartition t bs hp he))

theorem initialPartition_owner (t : Tree) (bs : List (List Nat)) (color : Nat → Nat)
    (hp : RMAF.partitionCheck (RMAF.leaves t) bs = true)
    (he : RMAF.pairwiseEmbeddings t bs = true) (v : RMAF.Vertex) :
    (initialPartition t bs color hp he).owner v = checkedOwner t bs v := by
  rfl

theorem initialPartition_monochromatic (t : Tree) (bs : List (List Nat)) (color : Nat → Nat)
    (hp : RMAF.partitionCheck (RMAF.leaves t) bs = true)
    (he : RMAF.pairwiseEmbeddings t bs = true)
    (hm : ∀ b, b ∈ bs → LabelMonochromatic color b) :
    Monochromatic (initialPartition t bs color hp he) id := by
  intro a b x y ha hb ho
  have hat : LeafAt (recolor color t) a x := by simpa only [←fromTree_skeleton color [] t] using ha
  have hbt : LeafAt (recolor color t) b y := by simpa only [←fromTree_skeleton color [] t] using hb
  obtain ⟨va,hva,hxa⟩ := (recolor_leaf color t a x).1 hat
  obtain ⟨vb,hvb,hxb⟩ := (recolor_leaf color t b y).1 hbt
  have heq : checkedOwner t bs a = checkedOwner t bs b := by
    simpa only [initialPartition_owner] using ho
  exact hxa.symm.trans ((checkedSourcePartition_monochromatic t bs hp he color hm _ _ _ _ hva hvb heq).trans hxb)

/-- End-to-end exact normalization consumer from the ordinary source checks.
Every original block survives by coarsening on the actual normalized graph;
every original taxon occurs in its quotient group's unchanged payload. -/
theorem checked_normalization_lift (t : Tree) (bs : List (List Nat)) (color : Nat → Nat)
    (hp : RMAF.partitionCheck (RMAF.leaves t) bs = true)
    (he : RMAF.pairwiseEmbeddings t bs = true)
    (hm : ∀ b, b ∈ bs → LabelMonochromatic color b) :
    ∃ Q : SourcePartition (skeleton (normalize (fromTree color [] t))),
      Monochromatic Q id ∧ ∃ f : RMAF.Vertex → RMAF.Vertex,
      (∀ v x, LeafAt t v x → ∃ g,
        GroupLeafAt (normalize (fromTree color [] t)) (f v) g ∧ x ∈ g.labels) ∧
      (∀ u v x y, LeafAt t u x → LeafAt t v y →
        (∃ b, b ∈ bs ∧ x ∈ b ∧ y ∈ b) → Q.owner (f u) = Q.owner (f v)) := by
  let P := initialPartition t bs color hp he
  obtain ⟨Q,hQ,f,hf,hr⟩ := normalize_source_transport _ P
    (initialPartition_monochromatic t bs color hp he hm)
  refine ⟨Q,hQ,f,?_,?_⟩
  · intro v x hv
    obtain ⟨g,hg,hlab⟩ := hf v _ (fromTree_group_leaf color [] t v x hv)
    exact ⟨g,hg,hlab x (by simp)⟩
  · intro u v x y hu hv hblock
    apply hr u v _ _ (fromTree_group_leaf color [] t u x hu) (fromTree_group_leaf color [] t v y hv)
    change (initialPartition t bs color hp he).owner u = (initialPartition t bs color hp he).owner v
    rw [initialPartition_owner,initialPartition_owner]
    exact (checkedSourcePartition_owner t bs hp he u v x y hu hv).2 hblock

end Universal233.Integration
