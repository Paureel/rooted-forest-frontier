import Crossing
import Rename
import Equivalence
namespace OrdinaryCommonSplit
open RMAF VertexGeometry BinaryExchange Universal233

/-- Every actual original final block crossing one original cut occupies its
child endpoint. Original target embedding disjointness allows at most one. -/
theorem crossing_blocks_unique (T S : Tree) (F : List (List Nat)) (p : RMAF.Vertex) (b : Bool)
    (ht : (leaves T).Nodup) (hF : agreement T S F=true)
    (K L : List Nat) (hK : K∈F) (hL : L∈F)
    (mK : mixed K ((PairGeometry.descendants T (p++[b])).contains ·)=true)
    (mL : mixed L ((PairGeometry.descendants T (p++[b])).contains ·)=true) : K=L := by
  have hh:=hF
  simp only [agreement,Bool.and_eq_true] at hh
  have hin : ∀ C∈F, ∀ x∈C, x∈leaves T := by
    intro C hC x hx
    exact RestrictionBridge.checked_label _ F hh.1.1.1.1 hC hx
  obtain ⟨⟨x,hx,hxd⟩,⟨y,hy,hyd⟩⟩ := (mixed_iff K _).1 mK
  obtain ⟨⟨u,hu,hud⟩,⟨v,hv,hvd⟩⟩ := (mixed_iff L _).1 mL
  have hEK := BothBad.crossing_occupies T p b K ht (hin K hK) x y hx hy
    (List.contains_iff_mem.1 hxd) (by intro hm;have hh := List.contains_iff_mem.2 hm;rw [hyd] at hh;contradiction)
  have hEL := BothBad.crossing_occupies T p b L ht (hin L hL) u v hu hv
    (List.contains_iff_mem.1 hud) (by intro hm;have hh := List.contains_iff_mem.2 hm;rw [hvd] at hh;contradiction)
  by_cases he : K=L
  · exact he
  · exact False.elim (RestrictionBridge.pairwise_distinct T F hh.1.2 K L hK hL he _ hEK hEL)

theorem edge_mixed_count (T S : Tree) (F : List (List Nat)) (p : RMAF.Vertex) (b : Bool)
    (ht : (leaves T).Nodup) (hF : agreement T S F=true) :
    (F.filter (mixed · ((PairGeometry.descendants T (p++[b])).contains ·))).length≤1 := by
  have hh:=hF
  simp only [agreement,Bool.and_eq_true] at hh
  apply marked_at_most_one F _ (fun C D => C≠D)
    (RestrictionBridge.checked_family_nodup (leaves T) F hh.1.1.1.1)
  intro C hC D hD hne hMC hMD
  exact hne (crossing_blocks_unique T S F p b ht hF C D hC hD hMC hMD)

theorem edge_split_count (T S : Tree) (F : List (List Nat)) (p : RMAF.Vertex) (b : Bool)
    (ht : (leaves T).Nodup) (hF : agreement T S F=true) :
    (splitAll F ((PairGeometry.descendants T (p++[b])).contains ·)).length≤F.length+1 := by
  have h := splitAll_length F ((PairGeometry.descendants T (p++[b])).contains ·)
  have count := edge_mixed_count T S F p b ht hF
  omega
end OrdinaryCommonSplit
