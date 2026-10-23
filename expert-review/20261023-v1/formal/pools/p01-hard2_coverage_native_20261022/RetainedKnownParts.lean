import RetainedPayment
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge OutputState Universal233
namespace ContactedHard2Survival

theorem whole_owned_exact (S : Tree) (P Q J : List (List Nat)) (A : List Nat) (s : Tree)
 (nd : (leaves S).Nodup) (partP : partitionCheck (leaves S) P=true)
 (partQ : partitionCheck (leaves S) Q=true) (refP : VertexGeometry.Refines P Q)
 (refJ : VertexGeometry.Refines J P) (aQ : A∈Q) (aJ : A∈J)
 (source : restrict A S=some s) : owned (sourceForest S P) A=[s] := by
 have neA:=partition_nonempty_member _ _ partQ A aQ
 have restrictions:=checked_restrictions S P nd partP
 have count:=materialized_owned_count S P A restrictions
 have one:=whole_parent_family_one (leaves S) P Q J A nd partP partQ refP refJ aQ aJ neA
 have all : ∀t,t∈owned (sourceForest S P) A→t=s := by
  intro t member
  have fields:=(mem_owned t _ _).mp member
  obtain ⟨D,dP,actual,labels,_,nonempty⟩:=(checked_materialization S P nd partP).2.2 t fields.1
  obtain ⟨U,uP,aSub⟩:=refJ A aJ
  have dSub : D⊆A:=fun x hx=>fields.2 (labels.mem_iff.mpr hx)
  obtain ⟨x,xD⟩:=List.exists_mem_of_ne_nil D (partition_nonempty_member _ _ partP D dP)
  have same:=group_unique (leaves S) P partP D U dP uP x xD (aSub _ (dSub xD))
  subst U
  have masks : ∀x,D.contains x=A.contains x := by
   intro x
   apply Bool.eq_iff_iff.mpr
   simpa only [List.contains_iff_mem] using (show x∈D ↔ x∈A from ⟨fun hx=>dSub hx,fun hx=>aSub _ hx⟩)
  have equal:=ContactedClade.restrict_ext S D A masks
  rw [actual,source] at equal
  exact Option.some.inj equal
 cases h : owned (sourceForest S P) A with
 | nil=>simp only [h,List.length_nil] at count;omega
 | cons t rest=>
  have ht:=all t (by rw [h];exact List.mem_cons_self)
  have restNil : rest=[]:=List.eq_nil_of_length_eq_zero (by simp only [h,List.length_cons] at count;omega)
  rw [ht,restNil]

theorem retained_knownOne_local (T S : Tree) (Q P J : List (List Nat)) (A : List Nat) (known : List (List Nat))
 (proper : DepthOne.proper T S=true) (parents : partitionCheck (leaves S) Q=true)
 (part : partitionCheck (leaves S) P=true) (emb : pairwiseEmbeddings S P=true)
 (refP : VertexGeometry.Refines P Q) (refJ : VertexGeometry.Refines J P)
 (aQ : A∈Q) (aJ : A∈J) (run : BothBad.knownOne T S A=some known) :
 agrees (localTarget (some T) A) (owned (sourceForest S P) A) known=true ∧ known.length=2 := by
 have pp:=IndependentReconstruction.proper_parts proper
 have scope:=output_parent_scope T S Q P proper parents part emb refP
 have lp:=local_proper (some T) (sourceForest S P) Q scope.1 scope.2.1 scope.2.2 A aQ
 unfold BothBad.knownOne at run
 cases ht : restrict A T with
 | none=>simp only [ht] at run;cases run
 | some t=>
  cases hs : restrict A S with
  | none=>simp only [ht,hs] at run;cases run
  | some s=>
   have exactSource:=whole_owned_exact S P Q J A s pp.2.1 part parents refP refJ aQ aJ hs
   have target : localTarget (some T) A=some t:=by simp only [localTarget,Option.bind_some,ht]
   rw [target,exactSource] at lp ⊢
   cases pre : DepthOne.pretest01 t s with
   | refused=>simp only [ht,hs,pre] at run;cases run
   | rejected=>simp only [ht,hs,pre] at run;cases run
   | found candidate=>
    cases candidate with
    | none=>simp only [ht,hs,pre] at run;cases run
    | some p=>
     have eq : DepthOne.forest s (some p)=known:=by simpa only [ht,hs,pre,Option.some.injEq] using run
     have valid:=(DepthOne.found_spec t s (some p) pre).2.2.1
     rw [←eq]
     exact ⟨(ForestState.initial_state_agreement_iff t s _ lp).mpr valid,by rfl⟩

theorem retained_good_parent_local (T S : Tree) (Q P J : List (List Nat)) (C : List Nat)
 (proper : DepthOne.proper T S=true) (parents : partitionCheck (leaves S) Q=true)
 (part : partitionCheck (leaves S) P=true) (emb : pairwiseEmbeddings S P=true)
 (refP : VertexGeometry.Refines P Q) (refJ : VertexGeometry.Refines J P)
 (cQ : C∈Q) (cJ : C∈J) (good : restrictionAgrees S T C=true) :
 agrees (localTarget (some T) C) (owned (sourceForest S P) C) [C]=true := by
 have pp:=IndependentReconstruction.proper_parts proper
 have scope:=output_parent_scope T S Q P proper parents part emb refP
 obtain ⟨s,hs,sl⟩:=checked_restrictions S Q pp.2.1 parents C cQ
 obtain ⟨t,ht,tl⟩:=checked_restrictions T Q pp.1 scope.2.1 C cQ
 have exactSource:=whole_owned_exact S P Q J C s pp.2.1 part parents refP refJ cQ cJ hs
 have target : localTarget (some T) C=some t:=by simp only [localTarget,Option.bind_some,ht]
 have lp:=local_proper (some T) (sourceForest S P) Q scope.1 scope.2.1 scope.2.2 C cQ
 rw [target,exactSource] at lp ⊢
 apply (ForestState.initial_state_agreement_iff t s [C] lp).mpr
 have sn:=(checked_materialization S Q pp.2.1 parents).2.2 s ((source_component S Q s).mpr ⟨C,cQ,hs⟩)
 have tn:=restricted_nodup T t C ht pp.1
 have sm:=restricted_nodup S s C hs pp.2.1
 have neC:=partition_nonempty_member _ _ parents C cQ
 have partS:=IndependentCommon.partition_from_flatten (leaves s) [C] sm
  (fun K member=>by
   have eq : K=C:=by simpa only [List.mem_cons,List.not_mem_nil,or_false] using member
   subst K
   exact neC)
  (by simpa only [List.flatten_cons,List.flatten_nil,List.append_nil] using sl.symm)
 have partT:=IndependentCommon.partition_from_flatten (leaves t) [C] tn
  (fun K member=>by
   have eq : K=C:=by simpa only [List.mem_cons,List.not_mem_nil,or_false] using member
   subst K
   exact neC)
  (by simpa only [List.flatten_cons,List.flatten_nil,List.append_nil] using tl.symm)
 have localGood:=ContactedHard2DP.materialized_good_local hs ht (fun _ hx=>hx) sl good
 have masks : ∀x,(leaves s).contains x=C.contains x := by
  intro x
  apply Bool.eq_iff_iff.mpr
  simpa only [List.contains_iff_mem] using sl.mem_iff
 change restrictionAgrees t s (leaves s)=true at localGood
 rw [ContactedHard2DP.restriction_mask t s (leaves s) C masks] at localGood
 simp only [agreement,partT,partS,List.all_cons,List.all_nil,pairwiseEmbeddings,localGood,
  Bool.and_self]
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.whole_owned_exact
#print axioms ContactedHard2Survival.whole_owned_exact
#check @ContactedHard2Survival.retained_knownOne_local
#print axioms ContactedHard2Survival.retained_knownOne_local
#check @ContactedHard2Survival.retained_good_parent_local
#print axioms ContactedHard2Survival.retained_good_parent_local
