import OutsideOne
namespace OrdinaryCommonSplit.Source
open RMAF Universal233 RestrictionBridge Caller

theorem three_clip_outside (d : Setup) (C : List Nat) (c : Nat)
    (hp : partitionCheck (leaves d.T) [d.X,C,[c]]=true) :
    clip d.Y [d.X,C,[c]]=[C,[c]] := by
  have nd := checked_family_nodup _ _ hp
  have neXC : d.X≠C := by
    intro e
    exact (List.nodup_cons.1 nd).1 (by simp [e])
  have neXc : d.X≠[c] := by
    intro e
    exact (List.nodup_cons.1 nd).1 (by simp [e])
  have offC := BinaryExchange.parent_disjoint _ _ hp d.X C (by simp) (by simp) neXC
  have offc := BinaryExchange.parent_disjoint _ _ hp d.X [c] (by simp) (by simp) neXc
  have subC : C⊆d.Y := by
    intro z hz
    have whole := checked_label _ _ hp (by simp : C∈[d.X,C,[c]]) hz
    rcases (split_labels _ d.X d.Y d.hpT z).1 whole with hX | hY
    · exact False.elim (offC z hX hz)
    · exact hY
  have cy : c∈d.Y := by
    have whole := checked_label _ _ hp (by simp : [c]∈[d.X,C,[c]]) (by simp : c∈[c])
    rcases (split_labels _ d.X d.Y d.hpT c).1 whole with hX | hY
    · exact False.elim (offc c hX (by simp))
    · exact hY
  have filterX : d.X.filter (d.Y.contains ·)=[] := by
    apply List.filter_eq_nil_iff.2
    intro z hz
    have outside := split_disjoint _ d.X d.Y d.hpT z hz
    simpa using outside
  have filterC := filter_subset_self d.Y C subC
  have nonempty : C.isEmpty=false := by
    have ne := checked_nonempty _ _ hp C (by simp)
    cases C with
    | nil => contradiction
    | cons x xs => rfl
  have noneX : clipBlock d.Y d.X=none := by simp only [clipBlock,filterX,List.isEmpty_nil,ite_true]
  have someC : clipBlock d.Y C=some C := by simp only [clipBlock,filterC,nonempty,Bool.false_eq_true,ite_false]
  have one : clipBlock d.Y [c]=some [c] := by simp [clipBlock,cy]
  simp only [clip,List.filterMap_cons,List.filterMap_nil,noneX,someC,one]


theorem actual_outside_one_from_three (d : Setup) (C : List Nat) (a b c : Nat) (r : RMAF.Vertex)
    (hp : partitionCheck (leaves d.T) [d.X,C,[c]]=true)
    (eT : pairwiseEmbeddings d.T [d.X,C,[c]]=true)
    (eS : pairwiseEmbeddings d.S [d.X,C,[c]]=true)
    (goodC : restrictionAgrees d.T d.S C=true)
    (cherry : HardParent.HasCherry a b d.T) (aY : a∈d.Y) (bY : b∈d.Y) (cY : c∈d.Y)
    (nonroot : r≠[]) (parent : r.dropLast∈minimalVertices [a,b] d.S)
    (outside : r∉minimalVertices [a,b] d.S) (cBelow : c∈HardParent.subtreeLabels d.S r) :
    agreement d.ty d.sy [C,[c]]=true ∧ IsMinimum d.ty d.sy 1 ∧
      ∃p,DepthOne.pretest01 d.ty d.sy=.found (some p) := by
  have clipEq := three_clip_outside d C c hp
  have cp := clip_partition d.T d.ty d.Y [d.X,C,[c]] d.hty hp
  have ny := checked_block_nodup _ _ d.hpT d.Y (by simp)
  have subY : d.Y⊆leaves d.T := fun _ h=>(split_labels _ d.X d.Y d.hpT _).2 (Or.inr h)
  have labels := restricted_perm d.T d.ty d.Y d.hty d.nt ny subY
  have partition : partitionCheck d.Y [C,[c]]=true := by
    rw [clipEq] at cp
    exact (partition_labels_congr (leaves d.ty) d.Y [C,[c]] (fun _=>labels.mem_iff)).1 cp
  have ceT := clip_embeddings d.T d.Y [d.X,C,[c]] eT
  have ceS := clip_embeddings d.S d.Y [d.X,C,[c]] eS
  rw [clipEq] at ceT ceS
  exact actual_outside_minimum_one d C a b c r partition ceT ceS goodC cherry aY bY cY nonroot parent outside cBelow
end OrdinaryCommonSplit.Source
