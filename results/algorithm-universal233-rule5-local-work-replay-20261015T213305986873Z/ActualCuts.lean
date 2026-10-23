import SourceBoundary
namespace OrdinaryCommonSplit.Source
open RMAF Universal233 CoreGraph RestrictionBridge

theorem original_split_from_incident (T : Tree) (X Y : List Nat) (q : RMAF.Vertex)
    (nd : (leaves T).Nodup) (hp : partitionCheck (leaves T) [X,Y]=true)
    (hi : incident T X=[q]) : OriginalSplit T X Y := by
  obtain ⟨⟨u,hu⟩,ne,side⟩ := actual_one_incident_split nd hi
  have nx := checked_block_nodup _ _ hp X (by simp)
  have ny := checked_block_nodup _ _ hp Y (by simp)
  have nu : (leaves u).Nodup := nd.sublist (DepthOne.subtree_leaves_sublist T u q hu)
  have subU : leaves u⊆leaves T := (DepthOne.subtree_leaves_sublist T u q hu).subset
  have labels : DepthOne.subtreeLabels T q=leaves u := by simp [DepthOne.subtreeLabels,hu]
  refine ⟨q,u,ne,hu,?_⟩
  rcases side with inside | outside
  · right
    apply (List.perm_ext_iff_of_nodup nu nx).2
    intro x
    constructor
    · intro hx
      exact (inside x (subU hx)).2 (by simpa only [labels] using hx)
    · intro hx
      have full := (split_labels _ X Y hp x).2 (Or.inl hx)
      simpa only [labels] using (inside x full).1 hx
  · left
    apply (List.perm_ext_iff_of_nodup nu ny).2
    intro x
    constructor
    · intro hx
      have full := subU hx
      have nx : x∉X := by
        intro hX
        have no := (outside x full).1 hX
        exact no (by simpa only [labels] using hx)
      exact ((split_labels _ X Y hp x).1 full).elim (fun h=>False.elim (nx h)) id
    · intro hx
      have full := (split_labels _ X Y hp x).2 (Or.inr hx)
      by_cases hu : x∈leaves u
      · exact hu
      · have hX := (outside x full).2 (by simpa only [labels] using hu)
        exact False.elim (split_disjoint _ X Y hp x hX hx)

theorem original_source_split (S u : Tree) (X Y : List Nat) (p : RMAF.Vertex)
    (nonroot : p≠[]) (hp : subtree S p=some u) (labels : (leaves u).Perm X) :
    OriginalSplit S X Y := ⟨p,u,nonroot,hp,Or.inr labels⟩
end OrdinaryCommonSplit.Source
