import ProjectedForest
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge

/-- Universal original-AF to marked-AF projection across an actual shared cut.
Both target and source original embeddings are checked after projection. The
chosen crossing block retains its block slot, so adding the explicit marker
costs NO additional component beyond the ordinary X restriction. -/
theorem original_marked_projection (T S mt ms : Tree) (X Y B : List Nat)
    (F : List (List Nat)) (y rho : Nat)
    (ndT : (leaves T).Nodup) (ndS : (leaves S).Nodup)
    (hpT : partitionCheck (leaves T) [X,Y]=true) (hpS : partitionCheck (leaves S) [X,Y]=true)
    (edgeT : OriginalSplit T X Y) (edgeS : OriginalSplit S X Y)
    (neX : B.filter (X.contains ·)≠[]) (neY : B.filter (Y.contains ·)≠[])
    (hy : y∈Y) (freshT : rho∉leaves T) (freshS : rho∉leaves S)
    (hmt : marked T X y rho=some mt) (hms : marked S X y rho=some ms)
    (ha : agreement T S (B::F)=true) :
    agreement mt ms (relabelForest (swap y rho) (projected X B F y))=true ∧
      (relabelForest (swap y rho) (projected X B F y)).length=(clip X (B::F)).length := by
  have hh := ha
  simp only [agreement,Bool.and_eq_true] at hh
  have nx : X.Nodup := checked_block_nodup (leaves T) [X,Y] hpT X (by simp)
  have hn : y∉X := by intro hx;exact split_disjoint _ X Y hpT y hx hy
  have hyT : y∈leaves T := (split_labels _ X Y hpT y).2 (Or.inr hy)
  have hyS : y∈leaves S := (split_labels _ X Y hpS y).2 (Or.inr hy)
  have subXT : X⊆leaves T := fun _ hx => (split_labels _ X Y hpT _).2 (Or.inl hx)
  have subXS : X⊆leaves S := fun _ hx => (split_labels _ X Y hpS _).2 (Or.inl hx)
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil X (checked_nonempty _ [X,Y] hpT X (by simp))
  obtain ⟨tx,htx⟩ := restriction_exists T X ⟨x,subXT hx,hx⟩
  have pclip : partitionCheck X (clip X (B::F))=true :=
    local_checked_labels T tx X [X,Y] _ ndT hpT (by simp) htx
      (clip_partition T tx X (B::F) htx hh.1.1.1.1)
  rw [clip_cons_nonempty X B F neX] at pclip
  have pproj := partition_attach_marker X (B.filter (X.contains ·)) (clip X F) y pclip hn
  have eT := projected_embeddings T X Y B F y ndT hpT edgeT hy neY hh.1.2
  have eS := projected_embeddings S X Y B F y ndS hpS edgeS hy neY hh.2
  have topo := projected_topologies T S X Y B F y rho ndT ndS hpT hpS edgeT edgeS
    neX neY hy freshT freshS ha
  cases hvT : restrict (y::X) T with
  | none => simp [marked,hvT] at hmt
  | some vT =>
    cases hvS : restrict (y::X) S with
    | none => simp [marked,hvS] at hms
    | some vS =>
      simp only [marked,hvT,Option.map_some,Option.some.injEq] at hmt
      simp only [marked,hvS,Option.map_some,Option.some.injEq] at hms
      subst mt;subst ms
      have subYT : y::X⊆leaves T := by
        intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hyT
        · exact subXT hz
      have subYS : y::X⊆leaves S := by
        intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hyS
        · exact subXS hz
      have ndU := List.nodup_cons.2 ⟨hn,nx⟩
      have hag := family_restrict_agrees T S vT vS (y::X) (projected X B F y) hvT hvS
        (restricted_perm T vT _ hvT ndT ndU subYT)
        (restricted_perm S vS _ hvS ndS ndU subYS) pproj eT eS topo
      refine ⟨?_,?_⟩
      · rw [agreement_relabel_swap]
        exact hag
      · rw [relabelForest_length,clip_cons_nonempty X B F neX]
        rfl

/-- The selected crossing component can occur anywhere in the literal
original forest, in any block order. The same projection count is retained. -/
theorem arbitrary_original_marked_projection (T S mt ms : Tree) (X Y B : List Nat)
    (F : List (List Nat)) (y rho : Nat)
    (ndT : (leaves T).Nodup) (ndS : (leaves S).Nodup)
    (hpT : partitionCheck (leaves T) [X,Y]=true) (hpS : partitionCheck (leaves S) [X,Y]=true)
    (edgeT : OriginalSplit T X Y) (edgeS : OriginalSplit S X Y)
    (hB : B∈F) (neX : B.filter (X.contains ·)≠[]) (neY : B.filter (Y.contains ·)≠[])
    (hy : y∈Y) (freshT : rho∉leaves T) (freshS : rho∉leaves S)
    (hmt : marked T X y rho=some mt) (hms : marked S X y rho=some ms)
    (ha : agreement T S F=true) :
    ∃ G,agreement mt ms G=true ∧ G.length=(clip X F).length := by
  have perm : F.Perm (B::F.erase B) := List.perm_cons_erase hB
  have hf := BinaryExchange.agreement_perm T S F _ perm ha
  have hr := original_marked_projection T S mt ms X Y B (F.erase B) y rho ndT ndS
    hpT hpS edgeT edgeS neX neY hy freshT freshS hmt hms hf
  refine ⟨relabelForest (swap y rho) (projected X B (F.erase B) y),hr.1,?_⟩
  rw [hr.2]
  exact (perm.filterMap (clipBlock X)).length_eq.symm
end OrdinaryCommonSplit
