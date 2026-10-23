import ForestOutputs
import WholeMass

namespace Universal233.PaidAssembly
open RMAF CoreProgram SourceCoverage VertexGeometry

/-- Equality of the independently constructed literal parent-tag colors. -/
theorem same_tagged_color (A B : List Nat) (ca cb cc : Nat → Nat) :
    Universal233.Assembly.taggedColor A B ca cb cc = WholeSourceMass.taggedColor A B ca cb cc := rfl

theorem same_joint_color (T : Tree) (v w : RMAF.Vertex) :
    Assembly.localColor T (.both v w) = WholeSourceMass.jointLabel T v w := rfl

def OutputWitness (S : Tree) (P F : List (List Nat)) (q : Nat) (o : Output) : Prop :=
  RefinesBlocks F o.partition ∧ RefinesBlocks o.partition P ∧
  partitionCheck (leaves S) o.partition = true ∧ pairwiseEmbeddings S o.partition = true ∧
  CutRealization.RealizedOutput S o ∧ o.sourceCuts.length ≤ q

def CliqueClearing (T : Tree) (Q : List (List Nat)) (A B C : List Nat) (v : RMAF.Vertex) : Prop :=
  (Assembly.ParentClears T Q B (.at v) ∧ Assembly.ParentClears T Q C (.at v)) ∨
  (Assembly.ParentClears T Q A (.at v) ∧ Assembly.ParentClears T Q C (.at v)) ∨
  (Assembly.ParentClears T Q A (.at v) ∧ Assembly.ParentClears T Q B (.at v))

def FourClearing (T : Tree) (Q : List (List Nat)) (A B C : List Nat) (v w : RMAF.Vertex) : Prop :=
  (Assembly.ParentClears T Q B (.at v) ∧ Assembly.ParentClears T Q C (.at w)) ∨
  Assembly.ParentClears T Q B (.both v w) ∨
  (Assembly.ParentClears T Q A (.at v) ∧ Assembly.ParentClears T Q C (.at w)) ∨
  (Assembly.ParentClears T Q A (.at v) ∧ Assembly.ParentClears T Q B (.at w))

def DiagonalClearing (T : Tree) (Q : List (List Nat)) (A B C : List Nat) (v w : RMAF.Vertex) : Prop :=
  Assembly.ParentClears T Q B (.both v w) ∨
  (Assembly.ParentClears T Q A (.at v) ∧ Assembly.ParentClears T Q C (.at w))

theorem partition_mass_interface (S T : Tree) (A B C : List Nat)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (ht : (leaves T).Nodup) (hl : ∀ x, x ∈ leaves S → x ∈ leaves T) :
    WholeSourceMass.WholeCall S T A B C := by
  obtain ⟨hab,hac,hbc⟩ := Assembly.parent_partition_disjoint S A B C hp
  refine ⟨⟨?_,hab,hac,hbc⟩,ht,hl,?_,?_,?_⟩
  · intro x
    constructor
    · exact Assembly.parent_cover S A B C hp x
    · intro h
      apply partitionCheck_subset _ [A,B,C] hp
      simpa using h
  · exact partitionCheck_nonempty _ _ hp A (by simp)
  · exact partitionCheck_nonempty _ _ hp B (by simp)
  · exact partitionCheck_nonempty _ _ hp C (by simp)

theorem occupied_of_internal (T : Tree) (D : List Nat) (v : RMAF.Vertex)
    (hs : ∀ x, x ∈ D → x ∈ leaves T)
    (hi : ¬selectedLeaves (leaves T) T v) (hv : v ∈ minimalVertices D T) :
    WholeSourceMass.Occupied D T v :=
  ⟨fun h => hi (selected_leaves_mono D (leaves T) T hs v h),hv⟩

theorem clique_list_cover (T S : Tree) (A B C : List Nat) (F : List (List Nat))
    (v : RMAF.Vertex) (q : Nat)
    (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
    (hl : ∀ x, x ∈ leaves S → x ∈ leaves T) (hf : agreement T S F = true)
    (hp : partitionCheck (leaves S) [A,B,C] = true) (hr : RefinesBlocks F [A,B,C])
    (hi : ¬selectedLeaves (leaves T) T v) (hq : F.length-1 ≤ q) :
    ∃ o, o ∈ WholeSourceMass.cliqueOutputs S T A B v q ∧ OutputWitness S [A,B,C] F q o ∧
      CliqueClearing T o.partition A B C v := by
  rcases Assembly.clique_forest_cover T S A B C F v q ht hs hl hf hp hr hi hq with h | h | h
  all_goals obtain ⟨o,ho,hfQ,hQP,hpart,hemb,hreal,hbudget,ha,hb,hc⟩ := h
  all_goals refine ⟨o,?_,⟨hfQ,hQP,hpart,hemb,hreal,hbudget⟩,?_⟩
  · apply List.mem_append.mpr; apply Or.inl; apply List.mem_append.mpr; exact Or.inl ho
  · exact Or.inl ⟨hb,hc⟩
  · apply List.mem_append.mpr; apply Or.inl; apply List.mem_append.mpr; exact Or.inr ho
  · exact Or.inr (Or.inl ⟨ha,hc⟩)
  · apply List.mem_append.mpr; exact Or.inr ho
  · exact Or.inr (Or.inr ⟨ha,hb⟩)

theorem four_list_cover (T S : Tree) (A B C : List Nat) (F : List (List Nat))
    (v w : RMAF.Vertex) (q : Nat)
    (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
    (hl : ∀ x, x ∈ leaves S → x ∈ leaves T) (hf : agreement T S F = true)
    (hp : partitionCheck (leaves S) [A,B,C] = true) (hr : RefinesBlocks F [A,B,C])
    (hi : ¬selectedLeaves (leaves T) T v) (hj : ¬selectedLeaves (leaves T) T w)
    (hq : F.length-1 ≤ q) :
    ∃ o, o ∈ WholeSourceMass.fourChainOutputs S T A B v w q ∧ OutputWitness S [A,B,C] F q o ∧
      FourClearing T o.partition A B C v w := by
  rcases Assembly.chain_forest_four_cover T S A B C F v w q ht hs hl hf hp hr hi hj hq with h | h | h | h
  all_goals obtain ⟨o,ho,hfQ,hQP,hpart,hemb,hreal,hbudget,ha,hb,hc⟩ := h
  all_goals refine ⟨o,?_,⟨hfQ,hQP,hpart,hemb,hreal,hbudget⟩,?_⟩
  · apply List.mem_append.mpr; apply Or.inl; apply List.mem_append.mpr; apply Or.inl
    apply List.mem_append.mpr; exact Or.inl ho
  · exact Or.inl ⟨hb,hc⟩
  · apply List.mem_append.mpr; apply Or.inl; apply List.mem_append.mpr; apply Or.inl
    apply List.mem_append.mpr; exact Or.inr ho
  · exact Or.inr (Or.inl hb)
  · apply List.mem_append.mpr; apply Or.inl; apply List.mem_append.mpr; exact Or.inr ho
  · exact Or.inr (Or.inr (Or.inl ⟨ha,hc⟩))
  · apply List.mem_append.mpr; exact Or.inr ho
  · exact Or.inr (Or.inr (Or.inr ⟨ha,hb⟩))

theorem diagonal_list_cover (T S : Tree) (A B C : List Nat) (F : List (List Nat))
    (v w : RMAF.Vertex) (q : Nat)
    (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
    (hl : ∀ x, x ∈ leaves S → x ∈ leaves T) (hf : agreement T S F = true)
    (hp : partitionCheck (leaves S) [A,B,C] = true) (hr : RefinesBlocks F [A,B,C])
    (hi : ¬selectedLeaves (leaves T) T v) (hj : ¬selectedLeaves (leaves T) T w)
    (hv : v ∈ minimalVertices B T) (hw : w ∈ minimalVertices B T)
    (hcount : (jointColors B T v w).length = 2) (hq : F.length-1 ≤ q) :
    ∃ o, o ∈ WholeSourceMass.diagonalOutputs S T A B v w q ∧ OutputWitness S [A,B,C] F q o ∧
      DiagonalClearing T o.partition A B C v w := by
  rcases Assembly.chain_forest_diagonal_cover T S A B C F v w q ht hs hl hf hp hr hi hj hv hw hcount hq with h | h
  all_goals obtain ⟨o,ho,hfQ,hQP,hpart,hemb,hreal,hbudget,ha,hb,hc⟩ := h
  all_goals refine ⟨o,?_,⟨hfQ,hQP,hpart,hemb,hreal,hbudget⟩,?_⟩
  · apply List.mem_append.mpr; exact Or.inl ho
  · exact Or.inl hb
  · apply List.mem_append.mpr; exact Or.inr ho
  · exact Or.inr ⟨ha,hc⟩


theorem clique_paid_cover (T S : Tree) (A B C : List Nat) (F : List (List Nat))
    (v : RMAF.Vertex) (q : Nat)
    (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
    (hl : ∀ x, x ∈ leaves S → x ∈ leaves T) (hf : agreement T S F = true)
    (hp : partitionCheck (leaves S) [A,B,C] = true) (hr : RefinesBlocks F [A,B,C])
    (hi : ¬selectedLeaves (leaves T) T v)
    (hA : v ∈ minimalVertices A T) (hB : v ∈ minimalVertices B T) (hC : v ∈ minimalVertices C T)
    (hq : F.length-1 ≤ q) (b : Rat) (hb : 2 ≤ b) :
    (∃ o, o ∈ WholeSourceMass.cliqueOutputs S T A B v q ∧ OutputWitness S [A,B,C] F q o ∧
      CliqueClearing T o.partition A B C v) ∧
    rawQMass b (WholeSourceMass.cliqueOutputs S T A B v q) ≤ 3*b^(-4 : Int) := by
  have hc := partition_mass_interface S T A B C hp ht hl
  obtain ⟨ha,hbb,hcc⟩ := WholeSourceMass.partition_target_support S T A B C hc.partition hl
  exact ⟨clique_list_cover T S A B C F v q ht hs hl hf hp hr hi hq,
    WholeSourceMass.clique_raw_mass S T A B C hc v (occupied_of_internal T A v ha hi hA)
      (occupied_of_internal T B v hbb hi hB) (occupied_of_internal T C v hcc hi hC) q b hb⟩

theorem four_paid_cover (T S : Tree) (A B C : List Nat) (F : List (List Nat))
    (v w : RMAF.Vertex) (q : Nat)
    (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
    (hl : ∀ x, x ∈ leaves S → x ∈ leaves T) (hf : agreement T S F = true)
    (hp : partitionCheck (leaves S) [A,B,C] = true) (hr : RefinesBlocks F [A,B,C])
    (hi : ¬selectedLeaves (leaves T) T v) (hj : ¬selectedLeaves (leaves T) T w)
    (hA : v ∈ minimalVertices A T) (hBv : v ∈ minimalVertices B T)
    (hBw : w ∈ minimalVertices B T) (hC : w ∈ minimalVertices C T)
    (hcount : 3 ≤ (jointColors B T v w).length) (hq : F.length-1 ≤ q) (b : Rat) (hb : 2 ≤ b) :
    (∃ o, o ∈ WholeSourceMass.fourChainOutputs S T A B v w q ∧ OutputWitness S [A,B,C] F q o ∧
      FourClearing T o.partition A B C v w) ∧
    rawQMass b (WholeSourceMass.fourChainOutputs S T A B v w q) ≤ 4*b^(-4 : Int) := by
  have hc := partition_mass_interface S T A B C hp ht hl
  obtain ⟨ha,hbb,hcc⟩ := WholeSourceMass.partition_target_support S T A B C hc.partition hl
  exact ⟨four_list_cover T S A B C F v w q ht hs hl hf hp hr hi hj hq,
    WholeSourceMass.four_chain_raw_mass S T A B C hc v w (occupied_of_internal T A v ha hi hA)
      (occupied_of_internal T B v hbb hi hBv) (occupied_of_internal T B w hbb hj hBw)
      (occupied_of_internal T C w hcc hj hC) hcount q b hb⟩

theorem diagonal_paid_cover (T S : Tree) (A B C : List Nat) (F : List (List Nat))
    (v w : RMAF.Vertex) (q : Nat)
    (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
    (hl : ∀ x, x ∈ leaves S → x ∈ leaves T) (hf : agreement T S F = true)
    (hp : partitionCheck (leaves S) [A,B,C] = true) (hr : RefinesBlocks F [A,B,C])
    (hi : ¬selectedLeaves (leaves T) T v) (hj : ¬selectedLeaves (leaves T) T w)
    (hA : v ∈ minimalVertices A T) (hBv : v ∈ minimalVertices B T)
    (hBw : w ∈ minimalVertices B T) (hC : w ∈ minimalVertices C T)
    (hcount : (jointColors B T v w).length = 2) (hq : F.length-1 ≤ q) (b : Rat) (hb : 2 ≤ b) :
    (∃ o, o ∈ WholeSourceMass.diagonalOutputs S T A B v w q ∧ OutputWitness S [A,B,C] F q o ∧
      DiagonalClearing T o.partition A B C v w) ∧
    rawQMass b (WholeSourceMass.diagonalOutputs S T A B v w q) ≤ b^(-3 : Int)+b^(-4 : Int) := by
  have hc := partition_mass_interface S T A B C hp ht hl
  obtain ⟨ha,_,hcc⟩ := WholeSourceMass.partition_target_support S T A B C hc.partition hl
  exact ⟨diagonal_list_cover T S A B C F v w q ht hs hl hf hp hr hi hj hBv hBw hcount hq,
    WholeSourceMass.diagonal_raw_mass S T A B C hc v w (occupied_of_internal T A v ha hi hA)
      (occupied_of_internal T C w hcc hj hC) hcount q b hb⟩

end Universal233.PaidAssembly
