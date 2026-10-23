import PrepareCommonTransport
import StrictGroupedSchedule
import OutputRun
open RMAF ForestState ForestGroups RestrictionBridge OutputState Universal233 PaidQueries GroupedFullQuery
namespace ContactedHard2Survival

theorem own_meterRun_value {P A : Type} (solve : P→Nat→Option (Nat×A)) (charge : P→Nat→Nat)
 (b : Nat) (js : List (Job P A)) : (meterRun solve charge b js).value=run solve b js := by
 induction js with
 | nil=>rfl
 | cons j js ih=>
  cases j with
  | resolved p c a=>simp only [meterRun,run,ih]
  | hard p=>cases h:solve p b <;>simp only [meterRun,run,h,ih]

theorem own_meterSchedule_value {P A : Type} (solve : P→Nat→Option (Nat×A)) (charge : P→Nat→Nat)
 (q : Nat) (js : List (Job P A)) : (meterSchedule solve charge q js).value=schedule solve q js := by
 by_cases prune : q<knownCost js+2*pending js
 · simp only [meterSchedule,schedule,ite_eq_left prune]
 · simp only [meterSchedule,schedule,ite_eq_right prune,own_meterRun_value]

theorem output_grouped_answer (ordinary : PaidInstances.OrdinarySolver) (q : Nat) (T S : Tree)
 (A B C : List Nat) (o : CoreProgram.Output)
 (below : PaidInstances.BelowBudget ordinary q) (proper : DepthOne.proper T S=true)
 (parents : partitionCheck (leaves S) [A,B,C]=true)
 (part : partitionCheck (leaves S) o.partition=true) (emb : pairwiseEmbeddings S o.partition=true)
 (refP : VertexGeometry.Refines o.partition [A,B,C])
 (payment : o.partition.length=o.sourceCuts.length+1) (positive : 0<o.sourceCuts.length)
 (ac : Clear (minimalVertices A T) (minimalVertices C T)) (bc : Clear (minimalVertices B T) (minimalVertices C T))
 (F : List (List Nat)) (agree : agreement T S F=true) (refF : VertexGeometry.Refines F o.partition)
 (budget : F.length-1≤q) :
 ∃G,(BothBadGrouped.runOutput (PaidInstances.OwnPaid ordinary q) T S A B C q o).answer?=some G ∧
 agreement T S G=true ∧ G.length≤F.length := by
 classical
 let ss:=sourceForest S o.partition
 let Q : List (List Nat):=[A++B,C]
 let ps:=groupProblems (some T) ss Q
 have scope:=output_group_scope T S A B C o.partition proper parents part emb refP
 have cross:=output_group_cross T S A B C o.partition proper parents part emb refP ac bc
 have localProper : ∀p,p∈ps→ForestState.proper p.target p.sources=true := by
  intro p hp
  obtain ⟨U,uQ,eq⟩:=List.mem_map.mp hp
  subst p
  exact local_proper (some T) ss Q scope.1 scope.2.1 scope.2.2 U uQ
 obtain ⟨js,prep⟩:=common_prepare_exists ps localProper
 have prepFacts:=common_prepare_spec ps js prep
 have keysND : (js.map Job.problem).Nodup := by
  rw [prepFacts.1]
  apply List.Pairwise.map (R:=fun U V : List Nat=>U≠V) (groupProblem (some T) ss)
   (fun U V diff eq=>diff (congrArg Problem.key eq))
  exact checked_family_nodup _ _ scope.2.1
 let H : Problem→List (List Nat):=fun p=>family p.key F
 have fa : agrees (some T) ss F=true :=
  (FreshResidual.residual_transfer_scope.1 T S o.partition F proper part emb).2.2.mpr ⟨agree,refF⟩
 have supports : ∀j,j∈js→valid j.problem (H j.problem) := by
  intro j hj
  have jp : j.problem∈ps := by rw [←prepFacts.1];exact List.mem_map.mpr ⟨j,hj,rfl⟩
  obtain ⟨U,uQ,eq⟩:=List.mem_map.mp jp
  rw [←eq]
  exact local_forward (some T) ss Q F fa scope.2.1 scope.2.2 U uQ
 have costFacts:=output_group_costs T S A B C o.partition o.sourceCuts.length proper parents part emb refP payment F agree refF
 have sumCosts : (js.map (fun j=>cost j.problem (H j.problem))).sum=
  additionalCost (owned ss (A++B)) (family (A++B) F)+additionalCost (owned ss C) (family C F) := by
  have mapped:=congrArg (fun ps : List Problem=>(ps.map (fun p=>cost p (H p))).sum) prepFacts.1
  dsimp only [ps] at mapped
  delta groupProblems at mapped
  simpa only [List.map_map,Q,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
   Nat.add_zero,groupProblem,cost,H,Function.comp_def] using mapped
 have affordable : o.sourceCuts.length≤q ∧ q-o.sourceCuts.length<q ∧
  (js.map (fun j=>cost j.problem (H j.problem))).sum≤q-o.sourceCuts.length := by
  rw [sumCosts]
  have count:=sources_le_blocks _ _ _ fa
  have sourceLen:=(FreshResidual.residual_transfer_scope.1 T S o.partition F proper part emb).1
  dsimp only [ss] at *
  omega
 obtain ⟨xs,f,scheduled,_,bound,fMap,validF⟩:=strict_grouped_schedule ordinary q (q-o.sourceCuts.length)
  below affordable.2.1 js prepFacts.2 keysND H supports affordable.2.2
 let G : List Nat→List (List Nat):=fun U=>(f (groupProblem (some T) ss U)).2
 have localG : ∀U,U∈Q→agrees (localTarget (some T) U) (owned ss U) (G U)=true := by
  intro U uQ
  have member : groupProblem (some T) ss U∈js.map Job.problem := by
   rw [prepFacts.1]
   exact List.mem_map.mpr ⟨U,uQ,rfl⟩
  obtain ⟨j,hj,eq⟩:=List.mem_map.mp member
  have fact:=validF j hj
  simpa only [eq,valid,groupProblem,G] using fact.1
 have global:=reverse_reconstruction (some T) ss Q G scope.1 scope.2.1 scope.2.2 cross localG
 have outEq : xs.flatMap Prod.snd=Q.flatMap G := by
  rw [←fMap,prepFacts.1]
  change ((Q.map (groupProblem (some T) ss)).map f).flatMap Prod.snd=Q.flatMap G
  simp only [List.flatMap_map,G]
 have original : agreement T S (Q.flatMap G)=true :=
  ((FreshResidual.residual_transfer_scope.1 T S o.partition (Q.flatMap G) proper part emb).2.2.mp global).1
 have costMap : answerCost xs=
  additionalCost (owned ss (A++B)) (G (A++B))+additionalCost (owned ss C) (G C) := by
  rw [←fMap,prepFacts.1]
  have each : ∀U,U∈Q→(f (groupProblem (some T) ss U)).1=additionalCost (owned ss U) (G U) := by
   intro U uQ
   have member : groupProblem (some T) ss U∈js.map Job.problem := by
    rw [prepFacts.1];exact List.mem_map.mpr ⟨U,uQ,rfl⟩
   obtain ⟨j,hj,eq⟩:=List.mem_map.mp member
   simpa only [eq,cost,groupProblem,G] using (validF j hj).2
  change answerCost ((Q.map (groupProblem (some T) ss)).map f)=_
  simp only [Q,List.map_cons,List.map_nil,answerCost,List.sum_cons,List.sum_nil,Nat.add_zero]
  rw [each (A++B) (by simp [Q]),each C (by simp [Q])]
 have lenS:=source_group_lengths (some T) ss Q scope.1 scope.2.1 scope.2.2
 have lenL:=sources_le_blocks _ _ _ (localG (A++B) (by simp [Q]))
 have lenR:=sources_le_blocks _ _ _ (localG C (by simp [Q]))
 have sourceLen:=(FreshResidual.residual_transfer_scope.1 T S o.partition F proper part emb).1
 have least : (Q.flatMap G).length≤F.length := by
  simp only [Q,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at lenS
  simp only [Q,List.flatMap_cons,List.flatMap_nil,List.length_append,List.append_nil]
  rw [costMap,sumCosts] at bound
  unfold additionalCost at bound costFacts
  dsimp only [ss] at lenS lenL lenR bound
  omega
 refine ⟨Q.flatMap G,?_,original,least⟩
 have jobs : BothBadGrouped.jobsFor T S A B C o=some js:=prep
 simp only [BothBadGrouped.runOutput,ite_eq_left affordable.1,jobs,BothBadGrouped.OutputResult.answer?,
  own_meterSchedule_value,scheduled,Option.map_some,outEq]
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.own_meterRun_value
#print axioms ContactedHard2Survival.own_meterRun_value
#check @ContactedHard2Survival.own_meterSchedule_value
#print axioms ContactedHard2Survival.own_meterSchedule_value
#check @ContactedHard2Survival.output_grouped_answer
#print axioms ContactedHard2Survival.output_grouped_answer
