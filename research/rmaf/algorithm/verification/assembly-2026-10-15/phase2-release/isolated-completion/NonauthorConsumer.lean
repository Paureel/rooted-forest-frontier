import HardPaid
namespace FreshAssemblyReview
open RMAF Universal233 CoreProgram SourceCoverage VertexGeometry PaidAssembly

def refineBool (F Q : List (List Nat)) : Bool :=
  F.all (fun b => Q.any (fun a => b.all a.contains))

theorem refineBool_sound (F Q : List (List Nat)) (h : refineBool F Q = true) : RefinesBlocks F Q := by
  intro b hb
  have he := List.all_eq_true.mp h b hb
  obtain ⟨a,ha,hs⟩ := List.any_eq_true.mp he
  exact ⟨a,ha,fun x hx => List.contains_iff_mem.mp (List.all_eq_true.mp hs x hx)⟩

theorem reverse_blocks (a b c d : List α) :
    (((a ++ b) ++ c) ++ d).Perm (((d ++ c) ++ b) ++ a) := by
  have h1 := List.perm_append_comm (l₁ := (a ++ b) ++ c) (l₂ := d)
  have h2 := (List.perm_append_comm (l₁ := a ++ b) (l₂ := c)).append_left d
  have h3 := ((List.perm_append_comm (l₁ := a) (l₂ := b)).append_left c).append_left d
  simpa only [List.append_assoc] using h1.trans (h2.trans h3)

def referenceFour (S T : Tree) (A B : List Nat) (v w : RMAF.Vertex) (q : Nat) : List Output :=
  ((WholeSourceMass.wholeOutputs S A B (colorLabel T v) (colorLabel T w) (fun _ => 0) q ++
    WholeSourceMass.wholeOutputs S A B (colorLabel T v) (fun _ => 0) (colorLabel T w) q) ++
    WholeSourceMass.wholeOutputs S A B (fun _ => 0) (WholeSourceMass.jointLabel T v w) (fun _ => 0) q) ++
    WholeSourceMass.wholeOutputs S A B (fun _ => 0) (colorLabel T v) (colorLabel T w) q

/-- Reference order differs; this universal Perm retains EVERY occurrence. -/
theorem actual_four_reference_permutation (S T : Tree) (A B : List Nat)
    (v w : RMAF.Vertex) (q : Nat) :
    (WholeSourceMass.fourChainOutputs S T A B v w q).Perm (referenceFour S T A B v w q) := by
  unfold WholeSourceMass.fourChainOutputs referenceFour
  exact reverse_blocks _ _ _ _

/-- The original fixed cut list is selected before F or its budget. Neither
parent refinement nor an emitted witness is a premise of this consumer. -/
theorem uniform_hard_clique_paid (T S : Tree) (v : RMAF.Vertex)
    (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
    (hl : ∀ x, x ∈ leaves S → x ∈ leaves T)
    {z : RMAF.Vertex} {a b : Nat} (hc : CoreGraph.CherryAt T z a b)
    (h2 : (HardParent.pendantOriginal S a b).length = 2)
    (hi : ¬selectedLeaves (leaves T) T v) :
    ∃ p r, HardParent.pendantOriginal S a b = [p,r] ∧
      ∀ F q, agreement T S F = true → F.length-1 ≤ q →
      v ∈ minimalVertices (leftParent S p) T →
      v ∈ minimalVertices (rightParent S r) T →
      v ∈ minimalVertices (rootParent S p r) T →
      ∀ c : Rat, 2 ≤ c →
      Hard2Covered S F a b p r q
        (WholeSourceMass.cliqueOutputs S T (leftParent S p) (rightParent S r) v q)
        (fun o => CliqueClearing T o.partition (leftParent S p) (rightParent S r) (rootParent S p r) v) ∧
      rawQMass c (WholeSourceMass.cliqueOutputs S T (leftParent S p) (rightParent S r) v q) ≤ 3*c^(-4 : Int) := by
  have he := List.eq_getElem_of_length_eq_two (HardParent.pendantOriginal S a b) h2
  refine ⟨_,_,he,?_⟩
  intro F q hf hq hA hB hC c hbase
  exact hard2_clique_paid T S F v q ht hs hl hf hc he hi hA hB hC hq c hbase

def target0 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.leaf 4)) (Tree.node (Tree.node (Tree.leaf 1) (Tree.leaf 3)) (Tree.leaf 5)))
def source0 : Tree := (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.node (Tree.leaf 2) (Tree.leaf 3)) (Tree.node (Tree.leaf 4) (Tree.leaf 5))))
theorem fixture_0_0 :
    (∃ o, o ∈ (WholeSourceMass.cliqueOutputs source0 target0 [0, 1] [2, 3] [] 4) ∧ OutputWitness source0 [[0, 1],[2, 3],[4, 5]] [[0, 1], [2], [3], [4], [5]] 4 o ∧
      CliqueClearing target0 o.partition [0, 1] [2, 3] [4, 5] []) ∧
    rawQMass (233/100) (WholeSourceMass.cliqueOutputs source0 target0 [0, 1] [2, 3] [] 4) ≤ 3*(233/100 : Rat)^(-4 : Int) := by
  apply clique_paid_cover target0 source0 [0, 1] [2, 3] [4, 5] [[0, 1], [2], [3], [4], [5]] [] 4
  · decide
  · decide
  · intro x hx
    simp only [source0,target0,leaves,List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hx ⊢
    omega
  · decide
  · decide
  · exact refineBool_sound _ _ (by decide)
  · simp [target0,selectedLeaves,Join]
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
theorem fixture_0_1 :
    (∃ o, o ∈ (WholeSourceMass.cliqueOutputs source0 target0 [0, 1] [2, 3] [] 4) ∧ OutputWitness source0 [[0, 1],[2, 3],[4, 5]] [[0], [1], [2, 3], [4], [5]] 4 o ∧
      CliqueClearing target0 o.partition [0, 1] [2, 3] [4, 5] []) ∧
    rawQMass (233/100) (WholeSourceMass.cliqueOutputs source0 target0 [0, 1] [2, 3] [] 4) ≤ 3*(233/100 : Rat)^(-4 : Int) := by
  apply clique_paid_cover target0 source0 [0, 1] [2, 3] [4, 5] [[0], [1], [2, 3], [4], [5]] [] 4
  · decide
  · decide
  · intro x hx
    simp only [source0,target0,leaves,List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hx ⊢
    omega
  · decide
  · decide
  · exact refineBool_sound _ _ (by decide)
  · simp [target0,selectedLeaves,Join]
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
theorem fixture_0_2 :
    (∃ o, o ∈ (WholeSourceMass.cliqueOutputs source0 target0 [0, 1] [2, 3] [] 4) ∧ OutputWitness source0 [[0, 1],[2, 3],[4, 5]] [[0], [1], [2], [3], [4, 5]] 4 o ∧
      CliqueClearing target0 o.partition [0, 1] [2, 3] [4, 5] []) ∧
    rawQMass (233/100) (WholeSourceMass.cliqueOutputs source0 target0 [0, 1] [2, 3] [] 4) ≤ 3*(233/100 : Rat)^(-4 : Int) := by
  apply clique_paid_cover target0 source0 [0, 1] [2, 3] [4, 5] [[0], [1], [2], [3], [4, 5]] [] 4
  · decide
  · decide
  · intro x hx
    simp only [source0,target0,leaves,List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hx ⊢
    omega
  · decide
  · decide
  · exact refineBool_sound _ _ (by decide)
  · simp [target0,selectedLeaves,Join]
  · decide
  · decide
  · decide
  · decide
  · decide +kernel

def target1 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.leaf 1)) (Tree.node (Tree.leaf 3) (Tree.node (Tree.leaf 4) (Tree.node (Tree.leaf 6) (Tree.leaf 5)))))
def source1 : Tree := (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.node (Tree.leaf 2) (Tree.node (Tree.leaf 3) (Tree.leaf 6))) (Tree.node (Tree.leaf 4) (Tree.leaf 5))))
theorem fixture_1_0 :
    (∃ o, o ∈ (WholeSourceMass.fourChainOutputs source1 target1 [0, 1] [2, 3, 6] [false, false] [true, true] 4) ∧ OutputWitness source1 [[0, 1],[2, 3, 6],[4, 5]] [[0], [1], [2, 3], [6], [4, 5]] 4 o ∧
      FourClearing target1 o.partition [0, 1] [2, 3, 6] [4, 5] [false, false] [true, true]) ∧
    rawQMass (233/100) (WholeSourceMass.fourChainOutputs source1 target1 [0, 1] [2, 3, 6] [false, false] [true, true] 4) ≤ 4*(233/100 : Rat)^(-4 : Int) := by
  apply four_paid_cover target1 source1 [0, 1] [2, 3, 6] [4, 5] [[0], [1], [2, 3], [6], [4, 5]] [false, false] [true, true] 4
  · decide
  · decide
  · intro x hx
    simp only [source1,target1,leaves,List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hx ⊢
    omega
  · decide
  · decide
  · exact refineBool_sound _ _ (by decide)
  · simp [target1,selectedLeaves,Join]
  · simp [target1,selectedLeaves,Join]
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
theorem fixture_1_1 :
    (∃ o, o ∈ (WholeSourceMass.fourChainOutputs source1 target1 [0, 1] [2, 3, 6] [false, false] [true, true] 4) ∧ OutputWitness source1 [[0, 1],[2, 3, 6],[4, 5]] [[0], [1], [2, 3, 6], [4], [5]] 4 o ∧
      FourClearing target1 o.partition [0, 1] [2, 3, 6] [4, 5] [false, false] [true, true]) ∧
    rawQMass (233/100) (WholeSourceMass.fourChainOutputs source1 target1 [0, 1] [2, 3, 6] [false, false] [true, true] 4) ≤ 4*(233/100 : Rat)^(-4 : Int) := by
  apply four_paid_cover target1 source1 [0, 1] [2, 3, 6] [4, 5] [[0], [1], [2, 3, 6], [4], [5]] [false, false] [true, true] 4
  · decide
  · decide
  · intro x hx
    simp only [source1,target1,leaves,List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hx ⊢
    omega
  · decide
  · decide
  · exact refineBool_sound _ _ (by decide)
  · simp [target1,selectedLeaves,Join]
  · simp [target1,selectedLeaves,Join]
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
theorem fixture_1_2 :
    (∃ o, o ∈ (WholeSourceMass.fourChainOutputs source1 target1 [0, 1] [2, 3, 6] [false, false] [true, true] 4) ∧ OutputWitness source1 [[0, 1],[2, 3, 6],[4, 5]] [[0, 1], [2], [3], [6], [4, 5]] 4 o ∧
      FourClearing target1 o.partition [0, 1] [2, 3, 6] [4, 5] [false, false] [true, true]) ∧
    rawQMass (233/100) (WholeSourceMass.fourChainOutputs source1 target1 [0, 1] [2, 3, 6] [false, false] [true, true] 4) ≤ 4*(233/100 : Rat)^(-4 : Int) := by
  apply four_paid_cover target1 source1 [0, 1] [2, 3, 6] [4, 5] [[0, 1], [2], [3], [6], [4, 5]] [false, false] [true, true] 4
  · decide
  · decide
  · intro x hx
    simp only [source1,target1,leaves,List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hx ⊢
    omega
  · decide
  · decide
  · exact refineBool_sound _ _ (by decide)
  · simp [target1,selectedLeaves,Join]
  · simp [target1,selectedLeaves,Join]
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
theorem fixture_1_3 :
    (∃ o, o ∈ (WholeSourceMass.fourChainOutputs source1 target1 [0, 1] [2, 3, 6] [false, false] [true, true] 4) ∧ OutputWitness source1 [[0, 1],[2, 3, 6],[4, 5]] [[0, 1], [2], [3, 6], [4], [5]] 4 o ∧
      FourClearing target1 o.partition [0, 1] [2, 3, 6] [4, 5] [false, false] [true, true]) ∧
    rawQMass (233/100) (WholeSourceMass.fourChainOutputs source1 target1 [0, 1] [2, 3, 6] [false, false] [true, true] 4) ≤ 4*(233/100 : Rat)^(-4 : Int) := by
  apply four_paid_cover target1 source1 [0, 1] [2, 3, 6] [4, 5] [[0, 1], [2], [3, 6], [4], [5]] [false, false] [true, true] 4
  · decide
  · decide
  · intro x hx
    simp only [source1,target1,leaves,List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hx ⊢
    omega
  · decide
  · decide
  · exact refineBool_sound _ _ (by decide)
  · simp [target1,selectedLeaves,Join]
  · simp [target1,selectedLeaves,Join]
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel

def target2 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.leaf 1)) (Tree.node (Tree.leaf 4) (Tree.node (Tree.leaf 3) (Tree.leaf 5))))
def source2 : Tree := (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.node (Tree.leaf 2) (Tree.leaf 3)) (Tree.node (Tree.leaf 4) (Tree.leaf 5))))
theorem fixture_2_0 :
    (∃ o, o ∈ (WholeSourceMass.diagonalOutputs source2 target2 [0, 1] [2, 3] [false, false] [true, true] 3) ∧ OutputWitness source2 [[0, 1],[2, 3],[4, 5]] [[0, 1], [2], [3], [4, 5]] 3 o ∧
      DiagonalClearing target2 o.partition [0, 1] [2, 3] [4, 5] [false, false] [true, true]) ∧
    rawQMass (233/100) (WholeSourceMass.diagonalOutputs source2 target2 [0, 1] [2, 3] [false, false] [true, true] 3) ≤ (233/100 : Rat)^(-3 : Int)+(233/100 : Rat)^(-4 : Int) := by
  apply diagonal_paid_cover target2 source2 [0, 1] [2, 3] [4, 5] [[0, 1], [2], [3], [4, 5]] [false, false] [true, true] 3
  · decide
  · decide
  · intro x hx
    simp only [source2,target2,leaves,List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hx ⊢
    omega
  · decide
  · decide
  · exact refineBool_sound _ _ (by decide)
  · simp [target2,selectedLeaves,Join]
  · simp [target2,selectedLeaves,Join]
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
theorem fixture_2_1 :
    (∃ o, o ∈ (WholeSourceMass.diagonalOutputs source2 target2 [0, 1] [2, 3] [false, false] [true, true] 4) ∧ OutputWitness source2 [[0, 1],[2, 3],[4, 5]] [[0], [1], [2, 3], [4], [5]] 4 o ∧
      DiagonalClearing target2 o.partition [0, 1] [2, 3] [4, 5] [false, false] [true, true]) ∧
    rawQMass (233/100) (WholeSourceMass.diagonalOutputs source2 target2 [0, 1] [2, 3] [false, false] [true, true] 4) ≤ (233/100 : Rat)^(-3 : Int)+(233/100 : Rat)^(-4 : Int) := by
  apply diagonal_paid_cover target2 source2 [0, 1] [2, 3] [4, 5] [[0], [1], [2, 3], [4], [5]] [false, false] [true, true] 4
  · decide
  · decide
  · intro x hx
    simp only [source2,target2,leaves,List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hx ⊢
    omega
  · decide
  · decide
  · exact refineBool_sound _ _ (by decide)
  · simp [target2,selectedLeaves,Join]
  · simp [target2,selectedLeaves,Join]
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel

end FreshAssemblyReview
