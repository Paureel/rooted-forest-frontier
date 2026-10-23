import PaidAssembly
import Safety

namespace Universal233.PaidAssembly
open RMAF CoreProgram SourceCoverage VertexGeometry

def leftParent (S : Tree) (p : RMAF.Vertex) : List Nat := HardParent.subtreeLabels S p
def rightParent (S : Tree) (r : RMAF.Vertex) : List Nat := HardParent.subtreeLabels S r
def rootParent (S : Tree) (p r : RMAF.Vertex) : List Nat :=
  (leaves S).filter fun x => !(leftParent S p).contains x && !(rightParent S r).contains x

/-- Exact original source graph safety consumed by the three forest constructors.
No F-refines-parents hypothesis is supplied. -/
theorem hard2_refinement_split {T S : Tree} {F : List (List Nat)}
    (hs : (leaves S).Nodup) (hf : agreement T S F = true)
    {z : RMAF.Vertex} {a b : Nat} (hc : CoreGraph.CherryAt T z a b)
    {p r : RMAF.Vertex} (hcuts : HardParent.pendantOriginal S a b = [p,r]) :
    HardParent.LiteralOriginalThree S p r ∧
      partitionCheck (leaves S) [leftParent S p,rightParent S r,rootParent S p r] = true ∧
      ([a] ∈ F ∨ [b] ∈ F ∨ RefinesBlocks F [leftParent S p,rightParent S r,rootParent S p r]) := by
  exact HardParent.actual_hard2_named_safety hs hf hc hcuts

theorem hard2_clique_named_cover (T S : Tree) (F : List (List Nat)) (v : RMAF.Vertex) (q : Nat)
    (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
    (hl : ∀ x, x ∈ leaves S → x ∈ leaves T) (hf : agreement T S F = true)
    {z : RMAF.Vertex} {a b : Nat} (hc : CoreGraph.CherryAt T z a b)
    {p r : RMAF.Vertex} (hcuts : HardParent.pendantOriginal S a b = [p,r])
    (hi : ¬selectedLeaves (leaves T) T v) (hq : F.length-1 ≤ q) :
    HardParent.LiteralOriginalThree S p r ∧
      partitionCheck (leaves S) [leftParent S p,rightParent S r,rootParent S p r] = true ∧
      ([a] ∈ F ∨ [b] ∈ F ∨
        ∃ o, o ∈ WholeSourceMass.cliqueOutputs S T (leftParent S p) (rightParent S r) v q ∧
          OutputWitness S [leftParent S p,rightParent S r,rootParent S p r] F q o ∧
          CliqueClearing T o.partition (leftParent S p) (rightParent S r) (rootParent S p r) v) := by
  obtain ⟨hgraph,hp,hcases⟩ := hard2_refinement_split hs hf hc hcuts
  refine ⟨hgraph,hp,?_⟩
  rcases hcases with ha | hb | hr
  · exact Or.inl ha
  · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr (clique_list_cover T S _ _ _ F v q ht hs hl hf hp hr hi hq))

/-- The named original source cuts are selected before quantifying over F. -/
theorem hard2_clique_uniform (T S : Tree) (v : RMAF.Vertex)
    (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
    (hl : ∀ x, x ∈ leaves S → x ∈ leaves T)
    {z : RMAF.Vertex} {a b : Nat} (hc : CoreGraph.CherryAt T z a b)
    (h2 : (HardParent.pendantOriginal S a b).length = 2)
    (hi : ¬selectedLeaves (leaves T) T v) :
    ∃ p r, HardParent.pendantOriginal S a b = [p,r] ∧
      ∀ F q, agreement T S F = true → F.length-1 ≤ q →
      HardParent.LiteralOriginalThree S p r ∧
      partitionCheck (leaves S) [leftParent S p,rightParent S r,rootParent S p r] = true ∧
      ([a] ∈ F ∨ [b] ∈ F ∨
        ∃ o, o ∈ WholeSourceMass.cliqueOutputs S T (leftParent S p) (rightParent S r) v q ∧
          OutputWitness S [leftParent S p,rightParent S r,rootParent S p r] F q o ∧
          CliqueClearing T o.partition (leftParent S p) (rightParent S r) (rootParent S p r) v) := by
  have he := List.eq_getElem_of_length_eq_two (HardParent.pendantOriginal S a b) h2
  exact ⟨_,_,he,fun F q hf hq => hard2_clique_named_cover T S F v q ht hs hl hf hc he hi hq⟩

theorem hard2_four_named_cover (T S : Tree) (F : List (List Nat)) (v w : RMAF.Vertex) (q : Nat)
    (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
    (hl : ∀ x, x ∈ leaves S → x ∈ leaves T) (hf : agreement T S F = true)
    {z : RMAF.Vertex} {a b : Nat} (hc : CoreGraph.CherryAt T z a b)
    {p r : RMAF.Vertex} (hcuts : HardParent.pendantOriginal S a b = [p,r])
    (hi : ¬selectedLeaves (leaves T) T v) (hj : ¬selectedLeaves (leaves T) T w)
    (hq : F.length-1 ≤ q) :
    HardParent.LiteralOriginalThree S p r ∧
      partitionCheck (leaves S) [leftParent S p,rightParent S r,rootParent S p r] = true ∧
      ([a] ∈ F ∨ [b] ∈ F ∨
        ∃ o, o ∈ WholeSourceMass.fourChainOutputs S T (leftParent S p) (rightParent S r) v w q ∧
          OutputWitness S [leftParent S p,rightParent S r,rootParent S p r] F q o ∧
          FourClearing T o.partition (leftParent S p) (rightParent S r) (rootParent S p r) v w) := by
  obtain ⟨hgraph,hp,hcases⟩ := hard2_refinement_split hs hf hc hcuts
  refine ⟨hgraph,hp,?_⟩
  rcases hcases with ha | hb | hr
  · exact Or.inl ha
  · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr (four_list_cover T S _ _ _ F v w q ht hs hl hf hp hr hi hj hq))

theorem hard2_diagonal_named_cover (T S : Tree) (F : List (List Nat)) (v w : RMAF.Vertex) (q : Nat)
    (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
    (hl : ∀ x, x ∈ leaves S → x ∈ leaves T) (hf : agreement T S F = true)
    {z : RMAF.Vertex} {a b : Nat} (hc : CoreGraph.CherryAt T z a b)
    {p r : RMAF.Vertex} (hcuts : HardParent.pendantOriginal S a b = [p,r])
    (hi : ¬selectedLeaves (leaves T) T v) (hj : ¬selectedLeaves (leaves T) T w)
    (hv : v ∈ minimalVertices (rightParent S r) T) (hw : w ∈ minimalVertices (rightParent S r) T)
    (hcount : (jointColors (rightParent S r) T v w).length = 2) (hq : F.length-1 ≤ q) :
    HardParent.LiteralOriginalThree S p r ∧
      partitionCheck (leaves S) [leftParent S p,rightParent S r,rootParent S p r] = true ∧
      ([a] ∈ F ∨ [b] ∈ F ∨
        ∃ o, o ∈ WholeSourceMass.diagonalOutputs S T (leftParent S p) (rightParent S r) v w q ∧
          OutputWitness S [leftParent S p,rightParent S r,rootParent S p r] F q o ∧
          DiagonalClearing T o.partition (leftParent S p) (rightParent S r) (rootParent S p r) v w) := by
  obtain ⟨hgraph,hp,hcases⟩ := hard2_refinement_split hs hf hc hcuts
  refine ⟨hgraph,hp,?_⟩
  rcases hcases with ha | hb | hr
  · exact Or.inl ha
  · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr (diagonal_list_cover T S _ _ _ F v w q ht hs hl hf hp hr hi hj hv hw hcount hq))

end Universal233.PaidAssembly
