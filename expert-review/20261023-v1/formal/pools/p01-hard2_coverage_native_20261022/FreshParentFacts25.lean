import ControlFlowV4
import BOForest
import GroupForwardProof
import GroupForward
import GroupRestriction
import OriginalReconstruction
import LocalSlots
import Optimality01
import LocalPaid08
import FreshMinimum21
import PreparedBridge23
open RMAF Universal233 PaidQueries RestrictionBridge
namespace FreshOrdinaryBridge
theorem parent_materializes (T S : Tree) (Q : List (List Nat))
    (pt : (leaves T).Nodup) (ps : (leaves S).Nodup)
    (hQT : partitionCheck (leaves T) Q=true) (hQS : partitionCheck (leaves S) Q=true) :
    ∃t s : List Nat→Tree,
      (∀U∈Q,restrict U T=some (t U)) ∧ (∀U∈Q,restrict U S=some (s U)) ∧
      ∀U∈Q,MafScheduler.properBlock T S U=true ∧ DepthOne.proper (t U) (s U)=true := by
  let t : List Nat→Tree:=fun U=>(restrict U T).getD (.leaf 0)
  let s : List Nat→Tree:=fun U=>(restrict U S).getD (.leaf 0)
  have ht : ∀U∈Q,restrict U T=some (t U) := by
    intro U hU
    obtain ⟨x,hx⟩:=List.exists_mem_of_ne_nil U (checked_nonempty (leaves T) Q hQT U hU)
    obtain ⟨u,hu⟩:=restriction_exists T U ⟨x,checked_label (leaves T) Q hQT hU hx,hx⟩
    simpa only [t,hu,Option.getD_some] using hu
  have hs : ∀U∈Q,restrict U S=some (s U) := by
    intro U hU
    obtain ⟨x,hx⟩:=List.exists_mem_of_ne_nil U (checked_nonempty (leaves S) Q hQS U hU)
    obtain ⟨u,hu⟩:=restriction_exists S U ⟨x,checked_label (leaves S) Q hQS hU hx,hx⟩
    simpa only [s,hu,Option.getD_some] using hu
  exact ⟨t,s,ht,hs,MafScheduler.checked_block_proper T S Q pt ps hQT hQS t s ht hs⟩

theorem parent_local_minima (Q : List (List Nat)) (t s : List Nat→Tree)
    (hp : ∀U∈Q,DepthOne.proper (t U) (s U)=true) :
    ∃m : List Nat→Nat,∀U∈Q,MafScheduler.LocalMinimum (t U) (s U) (m U) := by
  classical
  have ex : ∀U∈Q,∃n,MafScheduler.LocalMinimum (t U) (s U) n := by
    intro U hU
    exact local_minimum_from_AF (t U) (s U) _
      (OrdinaryDispatch.BudgetOptimization.singletons_agreement (t U) (s U) (hp U hU))
  let m : List Nat→Nat:=fun U=>if h:∃n,MafScheduler.LocalMinimum (t U) (s U) n then h.choose else 0
  refine ⟨m,?_⟩
  intro U hU
  have he:=ex U hU
  simpa only [m,dite_eq_left he] using he.choose_spec

-- This low-cost comparison is freshly assembled from candidate-only primitives.
-- It repeats the licensed bounded-forest argument, with zero new independence credit.
theorem found_local_minimum (T S : Tree) (c : Option Vertex)
    (h : DepthOne.pretest01 T S=.found c) :
    agreement T S (DepthOne.forest S c)=true ∧
      (DepthOne.forest S c).length-1=DepthOne.cutCost c ∧
      ∀F,agreement T S F=true → DepthOne.cutCost c≤F.length-1 := by
  obtain ⟨hp,hc,ha,least⟩:=DepthOne.found_spec T S c h
  refine ⟨ha,by cases c <;> simp [DepthOne.forest,DepthOne.cutCost],?_⟩
  intro F hF
  by_cases small : F.length-1≤1
  · obtain ⟨d,hd,hda,hbound⟩:=DepthOne.candidate_complete T S F
      ((DepthOne.proper_iff T S).mp hp).2.1 hF small
    exact Nat.le_trans (least d hd hda) hbound
  · have hc:=DepthOne.cutCost_le_one c
    omega

theorem slot_planned_fresh (T S : Tree) (t s : List Nat→Tree) (m : List Nat→Nat)
    (U : List Nat) (hb : MafScheduler.properBlock T S U=true)
    (ht : restrict U T=some (t U)) (hs : restrict U S=some (s U))
    (hp : DepthOne.proper (t U) (s U)=true) (hm : MafScheduler.LocalMinimum (t U) (s U) (m U)) :
    ∃j,MafScheduler.slot T S U=some j ∧ j.problem=U ∧ Planned m (MafScheduler.LocalValid t s m) j := by
  cases he : DepthOne.pretest01 (t U) (s U) with
  | refused =>
    have hh:=(DepthOne.refused_iff _ _).mp he
    simp only [hp] at hh
    cases hh
  | rejected =>
    obtain ⟨F,hF,hcost⟩:=hm.1
    have lower:=DepthOne.rejected_lower_bound _ _ he F hF
    refine ⟨.hard U,by simp [MafScheduler.slot,hb,ht,hs,he],rfl,?_⟩
    change 2≤m U
    omega
  | found c =>
    obtain ⟨ha,hcost,least⟩:=found_local_minimum (t U) (s U) c he
    obtain ⟨F,hF,hopt⟩:=hm.1
    have lower:=hm.2 _ ha
    have upper:=least F hF
    have hcm : DepthOne.cutCost c=m U := by omega
    refine ⟨.resolved U (DepthOne.cutCost c) (DepthOne.forest (s U) c),
      by simp [MafScheduler.slot,hb,ht,hs,he],rfl,?_⟩
    change DepthOne.cutCost c=m U ∧ MafScheduler.LocalValid t s m U (DepthOne.forest (s U) c) ∧ DepthOne.cutCost c≤1
    exact ⟨hcm,⟨ha,hcost.trans hcm⟩,DepthOne.cutCost_le_one c⟩

theorem prepare_planned_fresh (T S : Tree) (Q : List (List Nat))
    (t s : List Nat→Tree) (m : List Nat→Nat)
    (ht : ∀U∈Q,restrict U T=some (t U)) (hs : ∀U∈Q,restrict U S=some (s U))
    (hp : ∀U∈Q,MafScheduler.properBlock T S U=true ∧ DepthOne.proper (t U) (s U)=true)
    (hm : ∀U∈Q,MafScheduler.LocalMinimum (t U) (s U) (m U)) :
    ∃js,MafScheduler.prepare T S Q=some js ∧ js.map Job.problem=Q ∧
      ∀j∈js,Planned m (MafScheduler.LocalValid t s m) j := by
  induction Q with
  | nil => exact ⟨[],rfl,rfl,by simp⟩
  | cons U Q ih =>
    obtain ⟨tail,hprep,hkeys,hplan⟩:=ih (fun V hV=>ht V (by simp [hV]))
      (fun V hV=>hs V (by simp [hV])) (fun V hV=>hp V (by simp [hV])) (fun V hV=>hm V (by simp [hV]))
    obtain ⟨j,hj,hkey,hjplan⟩:=slot_planned_fresh T S t s m U (hp U (by simp)).1
      (ht U (by simp)) (hs U (by simp)) (hp U (by simp)).2 (hm U (by simp))
    refine ⟨j::tail,by simp [MafScheduler.prepare,hj,hprep],by simp [hkey,hkeys],?_⟩
    intro k hk
    rcases List.mem_cons.mp hk with rfl|hk
    · exact hjplan
    · exact hplan k hk

theorem total_keys_fresh {P A : Type} (m : P→Nat) (js : List (Job P A)) :
    totalMinimum m js=((js.map Job.problem).map m).sum := by
  induction js with
  | nil => rfl
  | cons j js ih => simpa only [totalMinimum,List.map_cons,List.sum_cons] using congrArg (m j.problem+·) ih

theorem sum_map_le_fresh {A : Type} (L : List A) (f g : A→Nat) (h : ∀x∈L,f x≤g x) :
    (L.map f).sum≤(L.map g).sum := by
  induction L with
  | nil => exact Nat.le_refl 0
  | cons x L ih =>
    have head:=h x (by simp)
    have tail:=ih (fun y hy=>h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons]
    omega

theorem refined_total_lower (T S : Tree) (Q : List (List Nat))
    (pt : (leaves T).Nodup) (ps : (leaves S).Nodup)
    (hQ : partitionCheck (leaves S) Q=true)
    (t s : List Nat→Tree) (m : List Nat→Nat)
    (ht : ∀U∈Q,restrict U T=some (t U)) (hs : ∀U∈Q,restrict U S=some (s U))
    (hm : ∀U∈Q,MafScheduler.LocalMinimum (t U) (s U) (m U))
    (js : List (Job (List Nat) MafScheduler.Forest)) (hkeys : js.map Job.problem=Q)
    (F : MafScheduler.Forest) (ha : agreement T S F=true) (href : Refines F Q) :
    totalMinimum m js≤F.length-Q.length := by
  rw [total_keys_fresh,hkeys]
  have lower:=sum_map_le_fresh Q m (fun U=>(family U F).length-1) (by
    intro U hU
    exact (hm U hU).2 _ (forward_local T S (t U) (s U) F Q U ha hQ href hU (ht U hU) (hs U hU)))
  have count:=(forward_decomposition T S F Q pt ps ha hQ href).2
  omega

theorem refined_parent_count (T S : Tree) (Q F : List (List Nat))
    (hQ : partitionCheck (leaves S) Q=true) (ha : agreement T S F=true)
    (href : Refines F Q) : Q.length≤F.length := by
  have hh:=ha
  simp only [agreement,Bool.and_eq_true] at hh
  have hF:=hh.1.1.1.2
  have positive : ∀U∈Q,0<(family U F).length := by
    intro U hU
    exact List.length_pos_iff.mpr (family_nonempty (leaves S) F Q hF hQ href U hU)
  have sum:=sum_sub_one Q (fun U=>(family U F).length) positive
  have total:=total_family_length (leaves S) F Q hF hQ href
  omega
end FreshOrdinaryBridge

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshOrdinaryBridge.parent_materializes
#print axioms FreshOrdinaryBridge.parent_materializes
#check @FreshOrdinaryBridge.parent_local_minima
#print axioms FreshOrdinaryBridge.parent_local_minima
#check @FreshOrdinaryBridge.found_local_minimum
#print axioms FreshOrdinaryBridge.found_local_minimum
#check @FreshOrdinaryBridge.slot_planned_fresh
#print axioms FreshOrdinaryBridge.slot_planned_fresh
#check @FreshOrdinaryBridge.prepare_planned_fresh
#print axioms FreshOrdinaryBridge.prepare_planned_fresh
#check @FreshOrdinaryBridge.total_keys_fresh
#print axioms FreshOrdinaryBridge.total_keys_fresh
#check @FreshOrdinaryBridge.sum_map_le_fresh
#print axioms FreshOrdinaryBridge.sum_map_le_fresh
#check @FreshOrdinaryBridge.refined_total_lower
#print axioms FreshOrdinaryBridge.refined_total_lower
#check @FreshOrdinaryBridge.refined_parent_count
#print axioms FreshOrdinaryBridge.refined_parent_count
