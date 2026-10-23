import SourceProgram
namespace OrdinaryCommonSplit.Source
open RMAF Universal233 CoreGraph HardParent RestrictionBridge Caller

/-- Actual original source path obstruction; no small minimum is assumed. -/
theorem outside_topology_obstruction (T S : Tree) (Y : List Nat) (a b c : Nat) (r : RMAF.Vertex)
    (ns : (leaves S).Nodup) (cherry : HasCherry a b T)
    (aY : a∈Y) (bY : b∈Y) (cY : c∈Y)
    (nonroot : r≠[]) (parent : r.dropLast∈minimalVertices [a,b] S)
    (outside : r∉minimalVertices [a,b] S) (cBelow : c∈HardParent.subtreeLabels S r) :
    restrictionAgrees T S Y=false := by
  cases h : restrictionAgrees T S Y with
  | false => rfl
  | true =>
    obtain ⟨t,ht,hc⟩ := restrict_hasCherry cherry Y aY bY
    cases hs : restrict Y S with
    | none => simp [restrictionAgrees,ht,hs] at h
    | some s =>
      have iso : RootedIso t s := (sameShape_correct t s).1 (by simpa [restrictionAgrees,ht,hs] using h)
      have excluded := prunedCherry_excluded (prunedCherry_of_restrict ns hs (iso_hasCherry iso hc))
      exact False.elim (excluded r nonroot parent outside c cBelow cY)

theorem one_minimum_from_actual_forest (T S : Tree) (F : Forest)
    (proper : DepthOne.proper T S=true) (af : agreement T S F=true) (cost : F.length-1=1)
    (different : sameShape T S=false) :
    IsMinimum T S 1 ∧ ∃p,DepthOne.pretest01 T S=.found (some p) := by
  obtain ⟨cut,hcut,aCut,cCut⟩ := DepthOne.pretest_complete T S proper F af (by omega)
  cases cut with
  | none =>
    obtain ⟨nt,ns,labels⟩ := (DepthOne.proper_iff T S).1 proper
    have rt := restrict_of_contains T (leaves S) (by intro x hx;exact List.contains_iff_mem.2 (labels.mem_iff.1 hx))
    have rs := restrict_of_contains S (leaves S) (by intro x hx;exact List.contains_iff_mem.2 hx)
    have top : sameShape T S=true := by
      have a := aCut
      simp only [agreement,Bool.and_eq_true] at a
      have h := List.all_eq_true.1 a.1.1.2 (leaves S) (by simp [DepthOne.forest])
      simpa [restrictionAgrees,rt,rs] using h
    simp [different] at top
  | some p => exact ⟨(found_one_minimum T S p hcut).2.2,⟨p,hcut⟩⟩

/-- Good core plus the literal other singleton supplies the actual one-cut
outside AF; original cherry/path geometry proves it cannot have cost zero. -/
theorem actual_outside_minimum_one (d : Setup) (C : List Nat) (a b c : Nat) (r : RMAF.Vertex)
    (partition : partitionCheck d.Y [C,[c]]=true)
    (eT : pairwiseEmbeddings d.T [C,[c]]=true) (eS : pairwiseEmbeddings d.S [C,[c]]=true)
    (goodC : restrictionAgrees d.T d.S C=true)
    (cherry : HasCherry a b d.T) (aY : a∈d.Y) (bY : b∈d.Y) (cY : c∈d.Y)
    (nonroot : r≠[]) (parent : r.dropLast∈minimalVertices [a,b] d.S)
    (outside : r∉minimalVertices [a,b] d.S) (cBelow : c∈HardParent.subtreeLabels d.S r) :
    agreement d.ty d.sy [C,[c]]=true ∧ IsMinimum d.ty d.sy 1 ∧
      ∃p,DepthOne.pretest01 d.ty d.sy=.found (some p) := by
  have ny := checked_block_nodup _ _ d.hpT d.Y (by simp)
  have sYT : d.Y⊆leaves d.T := fun _ h => (split_labels _ d.X d.Y d.hpT _).2 (Or.inr h)
  have sYS : d.Y⊆leaves d.S := fun _ h => (split_labels _ d.X d.Y d.hpS _).2 (Or.inr h)
  have lt := restricted_perm d.T d.ty d.Y d.hty d.nt ny sYT
  have ls := restricted_perm d.S d.sy d.Y d.hsy d.ns ny sYS
  have oneT := restrict_singleton d.T c d.nt (sYT cY)
  have oneS := restrict_singleton d.S c d.ns (sYS cY)
  have topo : ∀B∈[C,[c]],restrictionAgrees d.T d.S B=true := by
    intro B hB
    rcases List.mem_cons.1 hB with rfl | hB
    · exact goodC
    · have e : B=[c] := by simpa using hB
      subst B
      simp [restrictionAgrees,oneT,oneS,sameShape]
  have af := family_restrict_agrees d.T d.S d.ty d.sy d.Y [C,[c]] d.hty d.hsy lt ls partition eT eS topo
  have no := outside_topology_obstruction d.T d.S d.Y a b c r d.ns cherry aY bY cY nonroot parent outside cBelow
  have diff : sameShape d.ty d.sy=false := by simpa [restrictionAgrees,d.hty,d.hsy] using no
  have minimum := one_minimum_from_actual_forest d.ty d.sy [C,[c]] (outside_pair_proper d) af (by simp) diff
  exact ⟨af,minimum⟩
end OrdinaryCommonSplit.Source
