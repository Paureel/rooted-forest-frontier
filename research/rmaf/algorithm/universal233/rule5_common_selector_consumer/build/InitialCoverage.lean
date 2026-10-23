import CutCoverage

namespace Universal233.CutRealization
open RMAF CoreGraph CoreProgram Integration List

theorem checked_block_nonempty {T : Tree} {bs : List (List Nat)}
    (hp : partitionCheck (leaves T) bs = true) (b : List Nat) (hb : b ∈ bs) : b ≠ [] := by
  have hn : bs.all (fun b => !b.isEmpty) = true := by
    simp only [partitionCheck,Bool.and_eq_true] at hp
    exact hp.1.1
  have hh := List.all_eq_true.1 hn b hb
  intro he; simp [he] at hh

theorem checked_block_label {T : Tree} {bs : List (List Nat)}
    (hp : partitionCheck (leaves T) bs = true) {b : List Nat} (hb : b ∈ bs)
    {x : Nat} (hx : x ∈ b) : x ∈ leaves T := by
  have hs : bs.flatten.all (fun x => (leaves T).contains x) = true := by
    simp only [partitionCheck,Bool.and_eq_true] at hp
    exact hp.2
  exact List.contains_iff_mem.1 (List.all_eq_true.1 hs x (List.mem_flatten.2 ⟨b,hb,hx⟩))

noncomputable def blockRep (T : Tree) (b : List Nat) : RMAF.Vertex := by
  classical
  exact if h : ∃ a, ∃ x, LeafAt T a x ∧ x ∈ b then h.choose else []

theorem blockRep_spec {T : Tree} {bs : List (List Nat)}
    (hp : partitionCheck (leaves T) bs = true) {b : List Nat} (hb : b ∈ bs) :
    ∃ x, LeafAt T (blockRep T b) x ∧ x ∈ b := by
  classical
  have hne := checked_block_nonempty hp b hb
  cases b with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
    obtain ⟨a,ha⟩ := leaf_exists (checked_block_label hp hb (by simp : x ∈ x :: xs))
    have hh : ∃ a, ∃ y, LeafAt T a y ∧ y ∈ x :: xs := ⟨a,x,ha,by simp⟩
    simpa only [blockRep,dite_eq_left hh] using hh.choose_spec

theorem initial_owner_cover (T : Tree) (bs : List (List Nat)) (color : Nat → Nat)
    (hp : partitionCheck (leaves T) bs = true) (he : pairwiseEmbeddings T bs = true) :
    OwnerCover (fromTree color [] T) (initialPartition T bs color hp he) (bs.map (blockRep T)) := by
  constructor
  · intro r hr
    obtain ⟨b,hb,rfl⟩ := List.mem_map.1 hr
    obtain ⟨x,hx,hxb⟩ := blockRep_spec hp hb
    exact ⟨_,fromTree_group_leaf color [] T _ x hx⟩
  · intro v g hv
    have hsv := groupLeaf_skeleton _ v g hv
    rw [fromTree_skeleton] at hsv
    obtain ⟨x,hx,hcx⟩ := (recolor_leaf color T v g.color).1 hsv
    obtain ⟨b,hb,hxb⟩ := partitionCheck_covers _ bs hp x (leafAt_label T v x hx)
    obtain ⟨y,hy,hyb⟩ := blockRep_spec hp hb
    refine ⟨blockRep T b,List.mem_map.2 ⟨b,hb,rfl⟩,?_⟩
    change checkedOwner T bs (blockRep T b) = checkedOwner T bs v
    exact (checkedSourcePartition_owner T bs hp he _ _ y x hy hx).2 ⟨b,hb,hyb,hxb⟩

theorem initial_tracked (T : Tree) (bs : List (List Nat)) (color : Nat → Nat)
    (hp : partitionCheck (leaves T) bs = true) (he : pairwiseEmbeddings T bs = true) :
    Tracked bs (fromTree color [] T) [] (initialPartition T bs color hp he) := by
  intro b hb
  right
  refine ⟨checkedOwner T bs (blockRep T b),?_⟩
  intro x hx
  obtain ⟨v,hv⟩ := leaf_exists (checked_block_label hp hb hx)
  obtain ⟨y,hy,hyb⟩ := blockRep_spec hp hb
  refine ⟨v,⟨v,[x],color x⟩,?_,by simp,?_⟩
  · simpa using fromTree_group_leaf color [] T v x hv
  · change checkedOwner T bs v = checkedOwner T bs (blockRep T b)
    exact (checkedSourcePartition_owner T bs hp he _ _ x y hv hy).2 ⟨b,hb,hx,hyb⟩

def leafAddresses : GTree → List RMAF.Vertex
  | .leaf _ => [[]]
  | .node _ l r => (leafAddresses l).map (false :: ·) ++ (leafAddresses r).map (true :: ·)

theorem leafAddresses_exact (t : GTree) (v : RMAF.Vertex) :
    v ∈ leafAddresses t ↔ ∃ g, GroupLeafAt t v g := by
  induction t generalizing v with
  | leaf g => simpa [leafAddresses,groupLeaf_leaf] using (show v = [] ↔ ∃ a, v = [] ∧ g = a by simp)
  | node p l r ihl ihr =>
    cases v with
    | nil => simp [leafAddresses,GroupLeafAt,groupAt]
    | cons b v => cases b <;> simpa [leafAddresses,GroupLeafAt,groupAt] using (by
        first | exact ihl v | exact ihr v)

theorem all_leaves_cover (t : GTree) (P : SourcePartition (skeleton t)) :
    OwnerCover t P (leafAddresses t) :=
  ⟨fun v hv => (leafAddresses_exact t v).1 hv,
    fun v g hv => ⟨v,(leafAddresses_exact t v).2 ⟨g,hv⟩,rfl⟩⟩

theorem fromTree_leafAddresses_length (color : Nat → Nat) (p : RMAF.Vertex) (T : Tree) :
    (leafAddresses (fromTree color p T)).length = (leaves T).length := by
  induction T generalizing p with
  | leaf x => rfl
  | node l r ihl ihr => simp [fromTree,leafAddresses,leaves,ihl,ihr]

/-- The external ordinary source checks construct all finite-cover and original
refinement hypotheses. Budget is exactly components minus one, with no rho. -/
theorem generate_refinement_coverage (T : Tree) (bs : List (List Nat)) (color : Nat → Nat)
    (hn : (leaves T).Nodup) (hp : partitionCheck (leaves T) bs = true)
    (he : pairwiseEmbeddings T bs = true)
    (hm : ∀ b, b ∈ bs → VertexGeometry.LabelMonochromatic color b)
    (budget : Nat) (hb : bs.length - 1 ≤ budget) :
    ∃ o, o ∈ (generate T color budget).outputs ∧
      VertexGeometry.Refines bs o.partition ∧ RealizedOutput T o := by
  let P := initialPartition T bs color hp he
  have hP := initialPartition_monochromatic T bs color hp he hm
  have htrack := initial_tracked T bs color hp he
  have hex : ∃ reps, OwnerCover (fromTree color [] T) P reps ∧
      reps.length ≤ min budget ((leaves T).length - 1) + 1 := by
    by_cases hc : bs.length ≤ (leaves T).length
    · refine ⟨bs.map (blockRep T),initial_owner_cover T bs color hp he,?_⟩
      simp only [List.length_map]
      omega
    · refine ⟨leafAddresses (fromTree color [] T),all_leaves_cover _ P,?_⟩
      rw [fromTree_leafAddresses_length]
      omega
  obtain ⟨reps,hr,hq⟩ := hex
  obtain ⟨o,ho,href⟩ := run_refinement_coverage History.initial hn P hP reps hr htrack _ hq
  have hgen : o ∈ (generate T color budget).outputs := by simpa [generate,hn] using ho
  exact ⟨o,hgen,href,generate_original_realization T color budget o hgen⟩

end Universal233.CutRealization
