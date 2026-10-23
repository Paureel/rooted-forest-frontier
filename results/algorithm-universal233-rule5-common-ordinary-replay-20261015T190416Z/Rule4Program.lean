import Rule4Costs
import Equivalence

namespace Universal233.Rule4
open RMAF VertexGeometry CoreGraph Integration HardParent BinaryExchange CutRealization

def leafAddress (a : Nat) : Tree → Option RMAF.Vertex
  | .leaf x => if x = a then some [] else none
  | .node l r => match leafAddress a l with
    | some p => some (false :: p)
    | none => (leafAddress a r).map (true :: ·)

theorem leafAddress_sound {T : Tree} {a : Nat} {p : RMAF.Vertex}
    (h : leafAddress a T = some p) : LeafAt T p a := by
  induction T generalizing p with
  | leaf x =>
    by_cases he : x = a
    · subst x; have hp : p = [] := by simpa [leafAddress] using h.symm
      subst p; rfl
    · simp [leafAddress,he] at h
  | node l r il ir =>
    cases hl : leafAddress a l with
    | some q =>
      have hp : p = false :: q := by simpa [leafAddress,hl] using h.symm
      subst p; exact il hl
    | none =>
      cases hr : leafAddress a r with
      | none => simp [leafAddress,hl,hr] at h
      | some q =>
        have hp : p = true :: q := by simpa [leafAddress,hl,hr] using h.symm
        subst p; exact ir hr

theorem leafAddress_exists {T : Tree} {a : Nat} (ha : a ∈ leaves T) :
    ∃ p, leafAddress a T = some p := by
  induction T with
  | leaf x => have he : a = x := by simpa [leaves] using ha
              subst x; exact ⟨[],by simp [leafAddress]⟩
  | node l r il ir =>
    cases hl : leafAddress a l with
    | some p => exact ⟨false :: p,by simp [leafAddress,hl]⟩
    | none =>
      have har : a ∈ leaves r := by
        rcases List.mem_append.1 ha with hh | hh
        · obtain ⟨p,hp⟩ := il hh; simp [hl] at hp
        · exact hh
      obtain ⟨p,hp⟩ := ir har
      exact ⟨true :: p,by simp [leafAddress,hl,hp]⟩

def aHead {T S : Tree} (s : Choice T S) : RMAF.Vertex :=
  (leafAddress s.raw.a S).getD []

theorem aHead_leaf {T S : Tree} (s : Choice T S) : LeafAt S (aHead s) s.raw.a := by
  have ha := (hasCherry_labels (orderedCherries_sound s.admission.2.1)).1
  obtain ⟨p,hp⟩ := leafAddress_exists ha
  simpa [aHead,hp] using leafAddress_sound hp

theorem aHead_nonroot {T S : Tree} (s : Choice T S) : aHead s ≠ [] := by
  intro he
  have hl := aHead_leaf s
  rw [he] at hl
  have impossible : ∀ (U : Tree) (a c : Nat), LeafAt U [] a → HasCherry a c U → False := by
    intro U a c hleaf hcherry
    cases U with
    | leaf x => cases hcherry
    | node l r => simp [LeafAt,subtree] at hleaf
  exact impossible S s.raw.a s.raw.c hl (orderedCherries_sound s.admission.2.1)

structure Branch where
  target : Tree
  source : Tree
  cuts : List RMAF.Vertex
  swapped : Bool
  deriving Repr

def Branch.partition (b : Branch) := literalPartition b.source b.cuts
def Branch.sourceForest (b : Branch) := OutputState.sourceForest b.source b.partition
def Branch.cost (b : Branch) := b.cuts.length

def branches {T S : Tree} (s : Choice T S) : List Branch :=
  [⟨T,S,[s.raw.cHead,s.raw.xHead],false⟩,
   ⟨T,S,[aHead s],false⟩,
   ⟨S,T,pendantOriginal T s.raw.a s.raw.c,true⟩]

theorem literal_two (S : Tree) (q r : RMAF.Vertex) :
    literalPartition S [q,r] = literalThree S q r := by
  simp [literalPartition,literalThree]

theorem literal_leaf (S : Tree) {p : RMAF.Vertex} {a : Nat} (hp : LeafAt S p a) :
    literalPartition S [p] = isolatePartition S a := by
  have hl := subtreeLabels_at_leaf hp
  simp [literalPartition,isolatePartition,hl]
  congr 1

theorem selected_branches_cover {T S : Tree} (s : Choice T S) {F : List (List Nat)}
    (hF : agreement T S F = true) :
    ∃ G b, b ∈ branches s ∧ agreement T S G = true ∧ G.length ≤ F.length ∧
      VertexGeometry.Refines G b.partition := by
  obtain ⟨G,hG,hlen,hcov⟩ := selected_cover s hF
  rcases hcov with hc | hc | hc
  · exact ⟨G,⟨T,S,[s.raw.cHead,s.raw.xHead],false⟩,by simp [branches],hG,hlen,
      by simpa only [Branch.partition,literal_two] using hc⟩
  · exact ⟨G,⟨T,S,[aHead s],false⟩,by simp [branches],hG,hlen,
      by simpa only [Branch.partition,literal_leaf S (aHead_leaf s)] using hc⟩
  · exact ⟨G,⟨S,T,pendantOriginal T s.raw.a s.raw.c,true⟩,by simp [branches],hG,hlen,hc⟩

theorem selected_cut_properties {T S : Tree} (s : Choice T S) (b : Branch)
    (hb : b ∈ branches s) :
    (leaves b.target).Nodup ∧ (leaves b.source).Nodup ∧
    (∀ x, x ∈ leaves b.target ↔ x ∈ leaves b.source) ∧
    OriginalAntichain b.source b.cuts ∧
    (∃ a, a ∈ leaves b.source ∧ ∀ q, q ∈ b.cuts → a ∉ subtreeLabels b.source q) ∧
    0 < b.cost := by
  have hnT := s.priority.1
  have hnS := s.priority.2.1
  have heq : ∀ x, x ∈ leaves T ↔ x ∈ leaves S := fun x => s.priority.2.2.1.mem_iff
  have halT : s.raw.a ∈ leaves T := (hasCherry_labels (orderedCherries_sound s.admission.1)).1
  have halS : s.raw.a ∈ leaves S := (heq s.raw.a).1 halT
  have hblS : s.raw.b ∈ leaves S := (heq s.raw.b).1 (hasCherry_labels (orderedCherries_sound s.admission.1)).2
  have hq := two_cut_mem_left s.admission.2.2.2.1
  have hr := two_cut_mem_right s.admission.2.2.2.1
  have hp : (pendantOriginal S s.raw.a s.raw.b).Perm [s.raw.cHead,s.raw.xHead] := s.admission.2.2.2.1
  simp only [branches,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl
  · refine ⟨hnT,hnS,heq,?_,?_,by simp [Branch.cost]⟩
    · exact ⟨hp.nodup_iff.1 (pendantOriginal_nodup S _ _),
        by intro q hq'; exact ((pendantOriginal_spec S _ _ q).1 (hp.mem_iff.2 hq')).1,
        by intro q hq'; exact ((pendantOriginal_spec S _ _ q).1 (hp.mem_iff.2 hq')).2.1,
        by intro q r hq' hr' hne; exact pendant_incomparable (hp.mem_iff.2 hq') (hp.mem_iff.2 hr') hne⟩
    · exact ⟨s.raw.a,halS,by intro q hq'; exact source_label_outside_pendant (hp.mem_iff.2 hq') (Or.inl rfl) halS⟩
  · refine ⟨hnT,hnS,heq,?_,?_,by simp [Branch.cost]⟩
    · refine ⟨by simp,?_,?_,?_⟩
      · intro q hq'
        have hqe : q = aHead s := by simpa using hq'
        subst q
        exact (aHead_leaf s).valid
      · intro q hq'
        have hqe : q = aHead s := by simpa using hq'
        subst q
        exact aHead_nonroot s
      · intro q r hq' hr' hne; simp only [List.mem_singleton] at hq' hr'; exact False.elim (hne (hq'.trans hr'.symm))
    · refine ⟨s.raw.b,hblS,?_⟩
      intro q hq'
      have hqe : q = aHead s := by simpa using hq'
      subst q
      have hl := subtreeLabels_at_leaf (aHead_leaf s)
      simp [hl,Ne.symm s.admission.2.2.1]
  · refine ⟨hnS,hnT,(by intro x; exact (heq x).symm),pendant_antichain T _ _,?_,?_⟩
    · exact ⟨s.raw.a,halT,by intro q hq'; exact source_label_outside_pendant hq' (Or.inl rfl) halT⟩
    · have hm := selected_swapped_cost T S s; exact Nat.lt_of_lt_of_le (by decide) hm

/-- Literal output-state interface for EACH actually selected child, including
source swap, source-Q checks, source materialization and exact additional cost. -/
theorem selected_source_state {T S : Tree} (s : Choice T S) (b : Branch)
    (hb : b ∈ branches s) (F : List (List Nat)) :
    partitionCheck (leaves b.source) b.partition = true ∧
    pairwiseEmbeddings b.source b.partition = true ∧
    b.partition.length = b.cost + 1 ∧ b.sourceForest.length = b.partition.length ∧
    ForestState.proper (some b.target) b.sourceForest = true ∧
    (ForestState.agrees (some b.target) b.sourceForest F = true ↔
      agreement b.target b.source F = true ∧ RestrictionBridge.Refines F b.partition) ∧
    ForestState.additionalCost b.sourceForest F = F.length - b.partition.length := by
  obtain ⟨hnT,hnS,heq,hanti,⟨a,ha,hretain⟩,hpos⟩ := selected_cut_properties s b hb
  have hp := antichain_partition_checked hnS hanti ha hretain
  have he := antichain_source_embeddings hnS hanti
  exact ⟨hp,he,by simp [Branch.partition,Branch.cost,literalPartition],
    (OutputState.checked_materialization b.source b.partition hnS hp).1,
    OutputState.sourceForest_proper b.target b.source b.partition hnT hnS heq hp,
    OutputState.agrees_iff_original b.target b.source b.partition F hnT hnS heq hp he,
    OutputState.exact_additional_cost b.source b.partition F hnS hp⟩
end Universal233.Rule4
