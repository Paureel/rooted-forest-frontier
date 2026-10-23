import ControlFlowV4
import OriginalReconstruction
import LocalSlots
import FreshScheduler16
open RMAF Universal233 PaidQueries RestrictionBridge
namespace FreshOrdinaryBridge
theorem prepared_answer (solve : BothBad.ForestSolver) (T S : Tree)
    (Q : List (List Nat)) (b : Nat) (js : List (Job (List Nat) MafScheduler.Forest))
    (hprepare : MafScheduler.prepare T S Q=some js) :
    (BothBad.ordinaryExecution solve T S Q b).answer=
      ((schedule (MafScheduler.recursive T S (BothBad.asTree solve)) b js).answers.map
        (fun xs=>xs.flatMap Prod.snd)) := by
  unfold BothBad.ordinaryExecution
  rw [hprepare]
  change (meterSchedule (MafScheduler.recursive T S (BothBad.asTree solve)) (fun _ _=>0) b js).value.answers.map _=_
  rw [meter_schedule_value]

theorem recursive_sound_fixed (solve : BothBad.ForestSolver) (T S : Tree)
    (Q : List (List Nat)) (t s : List Nat→Tree) (m : List Nat→Nat) (b : Nat)
    (ht : ∀U∈Q,restrict U T=some (t U)) (hs : ∀U∈Q,restrict U S=some (s U))
    (hc : ∀U∈Q,∀F,BothBad.asTree solve (t U) (s U) b=some F →
      agreement (t U) (s U) F=true ∧ F.length-1=m U)
    (U : List Nat) (hU : U∈Q) (c : Nat) (F : MafScheduler.Forest)
    (hcall : MafScheduler.recursive T S (BothBad.asTree solve) U b=some (c,F)) :
    c=m U ∧ MafScheduler.LocalValid t s m U F := by
  unfold MafScheduler.recursive at hcall
  rw [ht U hU,hs U hU] at hcall
  change (BothBad.asTree solve (t U) (s U) b).map (fun G=>(G.length-1,G))=some (c,F) at hcall
  obtain ⟨G,hG,he⟩:=Option.map_eq_some_iff.mp hcall
  have hgF : G=F := (Prod.mk.inj he).2
  subst G
  have hcost : F.length-1=c := (Prod.mk.inj he).1
  have hh:=hc U hU F hG
  exact ⟨hcost.symm.trans hh.2,hh⟩

theorem prepared_sound (solve : BothBad.ForestSolver) (T S : Tree)
    (Q : List (List Nat)) (t s : List Nat→Tree) (m : List Nat→Nat)
    (b : Nat) (js : List (Job (List Nat) MafScheduler.Forest))
    (pt : (leaves T).Nodup) (ps : (leaves S).Nodup)
    (hQT : partitionCheck (leaves T) Q=true) (hQS : partitionCheck (leaves S) Q=true)
    (eT : pairwiseEmbeddings T Q=true) (eS : pairwiseEmbeddings S Q=true)
    (ht : ∀U∈Q,restrict U T=some (t U)) (hs : ∀U∈Q,restrict U S=some (s U))
    (hprepare : MafScheduler.prepare T S Q=some js) (hkeys : js.map Job.problem=Q)
    (hplan : ∀j∈js,Planned m (MafScheduler.LocalValid t s m) j)
    (hcallbacks : ∀U∈Q,∀F,BothBad.asTree solve (t U) (s U) (allocated b js)=some F →
      agreement (t U) (s U) F=true ∧ F.length-1=m U)
    (F : MafScheduler.Forest) (hr : (BothBad.ordinaryExecution solve T S Q b).answer=some F) :
    agreement T S F=true ∧ Refines F Q ∧ F.length-Q.length=totalMinimum m js ∧
      totalMinimum m js≤b := by
  rw [prepared_answer solve T S Q b js hprepare] at hr
  obtain ⟨xs,hxs,hF⟩:=Option.map_eq_some_iff.mp hr
  have hsound : ∀U,Job.hard U∈js → ∀c G,
      MafScheduler.recursive T S (BothBad.asTree solve) U (allocated b js)=some (c,G) →
        c=m U ∧ MafScheduler.LocalValid t s m U G := by
    intro U hU c G hcall
    have hmem : U∈Q := by rw [←hkeys]; exact List.mem_map.mpr ⟨.hard U,hU,rfl⟩
    exact recursive_sound_fixed solve T S Q t s m (allocated b js) ht hs hcallbacks U hmem c G hcall
  obtain ⟨hans,hcost,hle⟩:=schedule_sound_fixed m (MafScheduler.LocalValid t s m)
    (MafScheduler.recursive T S (BothBad.asTree solve)) b js hplan hsound xs hxs
  obtain ⟨hag,hcount,href⟩:=MafScheduler.answers_original_reconstruction T S Q pt ps hQT hQS eT eS
    t s m ht hs js xs hkeys hans
  rw [hF] at hag hcount href
  exact ⟨hag,href,hcount.trans hcost,hle⟩

theorem prepared_complete (solve : BothBad.ForestSolver) (T S : Tree)
    (Q : List (List Nat)) (t s : List Nat→Tree) (m : List Nat→Nat)
    (b : Nat) (js : List (Job (List Nat) MafScheduler.Forest))
    (ht : ∀U∈Q,restrict U T=some (t U)) (hs : ∀U∈Q,restrict U S=some (s U))
    (hprepare : MafScheduler.prepare T S Q=some js) (hkeys : js.map Job.problem=Q)
    (hplan : ∀j∈js,Planned m (MafScheduler.LocalValid t s m) j)
    (hcallbackSound : ∀U∈Q,∀F,BothBad.asTree solve (t U) (s U) (allocated b js)=some F →
      agreement (t U) (s U) F=true ∧ F.length-1=m U)
    (hcallbackComplete : ∀U∈Q,m U≤allocated b js →
      ∃F,BothBad.asTree solve (t U) (s U) (allocated b js)=some F)
    (hq : totalMinimum m js≤b) :
    ∃F,(BothBad.ordinaryExecution solve T S Q b).answer=some F := by
  have key (U : List Nat) (hU : Job.hard U∈js) : U∈Q := by
    rw [←hkeys]; exact List.mem_map.mpr ⟨.hard U,hU,rfl⟩
  obtain ⟨xs,hxs,_,_⟩:=schedule_complete_fixed m (MafScheduler.LocalValid t s m)
    (MafScheduler.recursive T S (BothBad.asTree solve)) b js hplan
    (fun U hU c F hcall=>recursive_sound_fixed solve T S Q t s m (allocated b js)
      ht hs hcallbackSound U (key U hU) c F hcall)
    (by
      intro U hU hbudget
      obtain ⟨F,hF⟩:=hcallbackComplete U (key U hU) hbudget
      refine ⟨(F.length-1,F),?_⟩
      unfold MafScheduler.recursive
      rw [ht U (key U hU),hs U (key U hU)]
      change (BothBad.asTree solve (t U) (s U) (allocated b js)).map _=_
      rw [hF]
      rfl) hq
  refine ⟨xs.flatMap Prod.snd,?_⟩
  rw [prepared_answer solve T S Q b js hprepare,hxs]
  rfl
end FreshOrdinaryBridge

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshOrdinaryBridge.prepared_answer
#print axioms FreshOrdinaryBridge.prepared_answer
#check @FreshOrdinaryBridge.recursive_sound_fixed
#print axioms FreshOrdinaryBridge.recursive_sound_fixed
#check @FreshOrdinaryBridge.prepared_sound
#print axioms FreshOrdinaryBridge.prepared_sound
#check @FreshOrdinaryBridge.prepared_complete
#print axioms FreshOrdinaryBridge.prepared_complete
