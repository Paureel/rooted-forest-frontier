import BothProgram
namespace Universal233.BothBad
open RMAF CoreProgram SourceCoverage VertexGeometry PairAssembly

theorem crossing_occupies (T : Tree) (p : RMAF.Vertex) (s : Bool) (K : List Nat)
    (ht : (leaves T).Nodup) (hin : ∀ x∈K, x∈leaves T)
    (x y : Nat) (hx : x∈K) (hy : y∈K)
    (hxd : x∈PairGeometry.descendants T (p++[s]))
    (hyd : y∉PairGeometry.descendants T (p++[s])) :
    p++[s]∈minimalVertices K T := by
  obtain ⟨a,ha⟩ := (singleton_selected_exists T x).2 (hin x hx)
  obtain ⟨b,hb⟩ := (singleton_selected_exists T y).2 (hin y hy)
  have hpa : Prefix (p++[s]) a := by
    have hh := (PairGeometry.descendants_mem T (p++[s]) x).1 hxd
    simpa only [PairGeometry.leafAddress_correct T x ht a ha] using hh.2
  have hpb : ¬Prefix (p++[s]) b := by
    intro hh
    apply hyd
    apply (PairGeometry.descendants_mem T (p++[s]) y).2
    exact ⟨hin y hy,by simpa only [PairGeometry.leafAddress_correct T y ht b hb] using hh⟩
  apply (minimalVertices_correct K T (p++[s])).2
  exact ⟨a,b,(selected_decompose_label K T a).2 ⟨x,hx,ha⟩,
    (selected_decompose_label K T b).2 ⟨y,hy,hb⟩,(PairGeometry.edge_cross_path p s a b hpa hpb).2⟩

theorem avoids_side_mono (T : Tree) (p : RMAF.Vertex) (s : Bool) (K : List Nat)
    (ht : (leaves T).Nodup) (hin : ∀ x∈K, x∈leaves T)
    (havoid : p++[s]∉minimalVertices K T) :
    LabelMonochromatic (sideColor (PairGeometry.descendants T (p++[s]))) K := by
  intro x y hx hy
  by_cases hxd : x∈PairGeometry.descendants T (p++[s])
  · by_cases hyd : y∈PairGeometry.descendants T (p++[s])
    · simp [sideColor,hxd,hyd]
    · exact False.elim (havoid (crossing_occupies T p s K ht hin x y hx hy hxd hyd))
  · by_cases hyd : y∈PairGeometry.descendants T (p++[s])
    · exact False.elim (havoid (crossing_occupies T p s K ht hin y x hy hx hyd hxd))
    · simp [sideColor,hxd,hyd]

theorem original_binary_parent_mono (T S : Tree) (F : List (List Nat)) (A B : List Nat)
    (p : RMAF.Vertex) (s : Bool) (ht : (leaves T).Nodup)
    (hF : agreement T S F=true) (hab : ∀ x, x∈A → x∈B → False) :
    (∀ K∈F, (∀ x, x∈K → x∈A) →
      LabelMonochromatic (sideColor (PairGeometry.descendants T (p++[s]))) K) ∨
    (∀ K∈F, (∀ x, x∈K → x∈B) →
      LabelMonochromatic (sideColor (PairGeometry.descendants T (p++[s]))) K) := by
  have hp : partitionCheck (leaves T) F=true := by
    have hh:=hF; simp only [agreement,Bool.and_eq_true] at hh; exact hh.1.1.1.1
  have hin : ∀ K∈F, ∀ x∈K, x∈leaves T := by
    intro K hK x hx
    exact partitionCheck_subset _ F hp (List.mem_flatten.2 ⟨K,hK,hx⟩)
  have hd := ownership_from_original_agreement T S F (Assembly.parentGroups F A B) hF
    (Assembly.parentGroups_belongs F A B) (Assembly.parentGroups_disjoint F A B)
  have howner := two_parent_ownership_cover (PieceHulls T (Assembly.parentGroups F A B)) hd 0 1 (by decide) (p++[s])
  rcases howner with hA | hB
  · left
    have hclear := Assembly.clears_A T F A B (p++[s]) ((pieceHulls_clear _ _ _ _).1 hA)
    intro K hK hKA
    exact avoids_side_mono T p s K ht (hin K hK) (hclear K hK hKA _ (by simp [Assembly.targets]))
  · right
    have hclear := Assembly.clears_B T F A B (p++[s]) hab ((pieceHulls_clear _ _ _ _).1 hB)
    intro K hK hKB
    exact avoids_side_mono T p s K ht (hin K hK) (hclear K hK hKB _ (by simp [Assembly.targets]))
end Universal233.BothBad
