import HardConsumer

namespace Universal233.PaidAssembly
open RMAF CoreProgram SourceCoverage VertexGeometry

/-- Conclusion-only certificate: a literal original hard2 graph and an actual
endpoint-or-generated-output cover. No safety/existence/mass property is input. -/
def Hard2Covered (S : Tree) (F : List (List Nat)) (a b : Nat) (p r : RMAF.Vertex)
    (q : Nat) (outputs : List Output) (clear : Output → Prop) : Prop :=
  HardParent.LiteralOriginalThree S p r ∧
  partitionCheck (leaves S) [leftParent S p,rightParent S r,rootParent S p r] = true ∧
  ([a] ∈ F ∨ [b] ∈ F ∨ ∃ o, o ∈ outputs ∧
    OutputWitness S [leftParent S p,rightParent S r,rootParent S p r] F q o ∧ clear o)

theorem hard2_clique_paid (T S : Tree) (F : List (List Nat)) (v : RMAF.Vertex) (q : Nat)
    (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
    (hl : ∀ x, x ∈ leaves S → x ∈ leaves T) (hf : agreement T S F = true)
    {z : RMAF.Vertex} {a b : Nat} (hc : CoreGraph.CherryAt T z a b)
    {p r : RMAF.Vertex} (hcuts : HardParent.pendantOriginal S a b = [p,r])
    (hi : ¬selectedLeaves (leaves T) T v)
    (hA : v ∈ minimalVertices (leftParent S p) T)
    (hB : v ∈ minimalVertices (rightParent S r) T)
    (hC : v ∈ minimalVertices (rootParent S p r) T)
    (hq : F.length-1 ≤ q) (c : Rat) (hbase : 2 ≤ c) :
    Hard2Covered S F a b p r q (WholeSourceMass.cliqueOutputs S T (leftParent S p) (rightParent S r) v q)
      (fun o => CliqueClearing T o.partition (leftParent S p) (rightParent S r) (rootParent S p r) v) ∧
    rawQMass c (WholeSourceMass.cliqueOutputs S T (leftParent S p) (rightParent S r) v q) ≤ 3*c^(-4 : Int) := by
  have hcover := hard2_clique_named_cover T S F v q ht hs hl hf hc hcuts hi hq
  have hm := partition_mass_interface S T _ _ _ hcover.2.1 ht hl
  obtain ⟨ha,hb,hcc⟩ := WholeSourceMass.partition_target_support S T _ _ _ hm.partition hl
  exact ⟨hcover,WholeSourceMass.clique_raw_mass S T _ _ _ hm v
    (occupied_of_internal T _ v ha hi hA) (occupied_of_internal T _ v hb hi hB)
    (occupied_of_internal T _ v hcc hi hC) q c hbase⟩

theorem hard2_four_paid (T S : Tree) (F : List (List Nat)) (v w : RMAF.Vertex) (q : Nat)
    (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
    (hl : ∀ x, x ∈ leaves S → x ∈ leaves T) (hf : agreement T S F = true)
    {z : RMAF.Vertex} {a b : Nat} (hc : CoreGraph.CherryAt T z a b)
    {p r : RMAF.Vertex} (hcuts : HardParent.pendantOriginal S a b = [p,r])
    (hi : ¬selectedLeaves (leaves T) T v) (hj : ¬selectedLeaves (leaves T) T w)
    (hA : v ∈ minimalVertices (leftParent S p) T)
    (hBv : v ∈ minimalVertices (rightParent S r) T)
    (hBw : w ∈ minimalVertices (rightParent S r) T)
    (hC : w ∈ minimalVertices (rootParent S p r) T)
    (hcount : 3 ≤ (jointColors (rightParent S r) T v w).length)
    (hq : F.length-1 ≤ q) (c : Rat) (hbase : 2 ≤ c) :
    Hard2Covered S F a b p r q (WholeSourceMass.fourChainOutputs S T (leftParent S p) (rightParent S r) v w q)
      (fun o => FourClearing T o.partition (leftParent S p) (rightParent S r) (rootParent S p r) v w) ∧
    rawQMass c (WholeSourceMass.fourChainOutputs S T (leftParent S p) (rightParent S r) v w q) ≤ 4*c^(-4 : Int) := by
  have hcover := hard2_four_named_cover T S F v w q ht hs hl hf hc hcuts hi hj hq
  have hm := partition_mass_interface S T _ _ _ hcover.2.1 ht hl
  obtain ⟨ha,hb,hcc⟩ := WholeSourceMass.partition_target_support S T _ _ _ hm.partition hl
  exact ⟨hcover,WholeSourceMass.four_chain_raw_mass S T _ _ _ hm v w
    (occupied_of_internal T _ v ha hi hA) (occupied_of_internal T _ v hb hi hBv)
    (occupied_of_internal T _ w hb hj hBw) (occupied_of_internal T _ w hcc hj hC) hcount q c hbase⟩

theorem hard2_diagonal_paid (T S : Tree) (F : List (List Nat)) (v w : RMAF.Vertex) (q : Nat)
    (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
    (hl : ∀ x, x ∈ leaves S → x ∈ leaves T) (hf : agreement T S F = true)
    {z : RMAF.Vertex} {a b : Nat} (hc : CoreGraph.CherryAt T z a b)
    {p r : RMAF.Vertex} (hcuts : HardParent.pendantOriginal S a b = [p,r])
    (hi : ¬selectedLeaves (leaves T) T v) (hj : ¬selectedLeaves (leaves T) T w)
    (hA : v ∈ minimalVertices (leftParent S p) T)
    (hBv : v ∈ minimalVertices (rightParent S r) T)
    (hBw : w ∈ minimalVertices (rightParent S r) T)
    (hC : w ∈ minimalVertices (rootParent S p r) T)
    (hcount : (jointColors (rightParent S r) T v w).length = 2)
    (hq : F.length-1 ≤ q) (c : Rat) (hbase : 2 ≤ c) :
    Hard2Covered S F a b p r q (WholeSourceMass.diagonalOutputs S T (leftParent S p) (rightParent S r) v w q)
      (fun o => DiagonalClearing T o.partition (leftParent S p) (rightParent S r) (rootParent S p r) v w) ∧
    rawQMass c (WholeSourceMass.diagonalOutputs S T (leftParent S p) (rightParent S r) v w q) ≤ c^(-3 : Int)+c^(-4 : Int) := by
  have hcover := hard2_diagonal_named_cover T S F v w q ht hs hl hf hc hcuts hi hj hBv hBw hcount hq
  have hm := partition_mass_interface S T _ _ _ hcover.2.1 ht hl
  obtain ⟨ha,_,hcc⟩ := WholeSourceMass.partition_target_support S T _ _ _ hm.partition hl
  exact ⟨hcover,WholeSourceMass.diagonal_raw_mass S T _ _ _ hm v w
    (occupied_of_internal T _ v ha hi hA) (occupied_of_internal T _ w hcc hj hC) hcount q c hbase⟩

end Universal233.PaidAssembly
