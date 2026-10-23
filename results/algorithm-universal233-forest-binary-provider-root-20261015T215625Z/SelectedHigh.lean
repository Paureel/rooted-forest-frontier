import Symmetry
namespace Universal233.BinaryCheap
open RMAF CoreProgram SourceCoverage VertexGeometry BinaryExchange PairAssembly RankDichotomy RankConsumer

theorem selected_two_high (S T : Tree) (A B C : List Nat)
    (e : RMAF.Vertex × RMAF.Vertex)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (hl : ∀ x, x ∈ leaves S → x ∈ leaves T)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (hchoose : PairGeometry.choose T A B = some (.edge e))
    (hA : fourAccepted S (cheapColor A B (PairGeometry.descendants T e.2)) = false)
    (hB : fourAccepted S (cheapColor B A (PairGeometry.descendants T e.2)) = false)
    (q : Nat) (c : Rat) (hc : 2 ≤ c) :
    (∀ o, o ∈ sideOutputs S B A (PairGeometry.descendants T e.2) q ++
      sideOutputs S A B (PairGeometry.descendants T e.2) q → 4 ≤ o.sourceCuts.length) ∧
    rawQMass c (sideOutputs S B A (PairGeometry.descendants T e.2) q ++
      sideOutputs S A B (PairGeometry.descendants T e.2) q) ≤ 4*c^(-4 : Int) := by
  obtain ⟨u,hu,hay,han,hby,hbn,_⟩ := edge_facts T A B e hchoose
  have hcolor : ∀ X Y, cheapColor X Y (PairGeometry.descendants T e.2) = cheapColor X Y (leaves u) := by
    intro X Y
    funext x
    simp only [cheapColor,WholeSourceMass.taggedColor,sideColor,FreshPairReview.descendants_treeAt T u e.2 ht hu x]
  rw [hcolor] at hA hB
  rw [side_outputs_descendant S T u B A e.2 ht hu q,side_outputs_descendant S T u A B e.2 ht hu q]
  exact two_high S T A B C (leaves u) hs ht hl hp hay han hby hbn hA hB q c hc
end Universal233.BinaryCheap
