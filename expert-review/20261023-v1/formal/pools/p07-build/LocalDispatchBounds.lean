import LocalPlanPayload
namespace OrdinaryDispatch.Hard2SourceWork.LocalDispatchEnvelope
open RMAF Universal233 WholeSourceWork CoreWork ForestGroups
open GenericForest.CheckCorrespondence GenericForest.FrontierWork
open Universal233.BothBad Universal233.PaidQueries Universal233.Rule5SelectedLocalWork
open OrdinaryDispatch.WorkIntegration OrdinaryDispatch.FullSourceWork

def payloadSize (N : Nat) := 2*N*N+4*N+4
def materialPolynomial (N : Nat) := (4*(N+2)*N+3)*N+1
def dispatchPolynomial (N : Nat) := ordinaryLocalPolynomial N N+materialPolynomial N+
 16*(N+1)^2+64*(N+1)^3+2*N+64

theorem ordinaryPolynomial_mono (N L : Nat) (h:L≤N) :
 ordinaryLocalPolynomial N L≤ordinaryLocalPolynomial N N := by
 have a:=Nat.mul_le_mul_left (ordinarySlotPolynomial N+8) h
 have b:=Nat.mul_le_mul_left 128 (Nat.add_le_add_right h 1)
 have c:=Nat.mul_le_mul_left (64*(N+1)^2) h
 have d:=Nat.mul_le_mul_left (2*N+12) h
 have e:=Nat.mul_le_mul_left (32*(N+1)^2+12) h
 simp only [ordinaryLocalPolynomial];omega

theorem ordinaryQueries_count (T S : Tree) (qs : List (List Nat×Nat)) :
 (ordinaryQueriesMeter T S qs).value.length≤qs.length := by
 rw [ordinaryQueriesMeter_value]
 exact List.length_filterMap_le _ _

theorem ordinaryLocal_count (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree) (P : List (List Nat)) (b : Nat) :
 (ordinaryLocalSource actual T S P b).value.calls.length≤P.length := by
 simp only [ordinaryLocalSource,ordinaryPrepareMeter_value]
 cases hp:MafScheduler.prepare T S P with
 | none=>simp
 | some js=>
   have a:=ordinaryQueries_count T S (scheduleSourceMeter (mafRecursiveMeter actual T S) b js).queries
   have c:=scheduleSourceMeter_queries_bound (mafRecursiveMeter actual T S) b js
   have l:=prepare_length T S P js hp
   simp only []
   omega

theorem callback_local_payload (actual : GenericForest.FrontierWork.Ordinary) (T : Tree) (U : List Nat) (ss : List Tree)
 (b N : Nat) (tn:treeNodes T≤N) (F : List (List Nat))
 (h:GenericForest.solve actual (localTargetMeter (some T) U).value ss b=some F) :
 F.length≤N ∧ F.flatten.length≤N := by
 have pay:=state_payload_forest_return actual _ ss b F h
 have cap:=localTarget_labels_cap T U N tn
 rw [localTargetMeter_value] at pay
 exact ⟨Nat.le_trans pay.1 cap,Nat.le_trans pay.2 cap⟩

theorem reconstruction_bound (actual : GenericForest.FrontierWork.Ordinary) (T : Tree) (U : List Nat) (ss : List Tree)
 (known : List (List Nat)) (completed : List Nat) (b N : Nat)
 (tn:treeNodes T≤N) (kl:known.length≤2) :
 (retainedReconstructionMeter known completed
  (GenericForest.solve actual (localTargetMeter (some T) U).value ss b)).work≤2*N+24 := by
 cases h:GenericForest.solve actual (localTargetMeter (some T) U).value ss b with
 | none=>simp [retainedReconstructionMeter]
 | some F=>have p:=callback_local_payload actual T U ss b N tn F h
           simp only [retainedReconstructionMeter];omega

theorem dispatch_payload (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree) (e : Entry) (N : Nat)
 (three:3≤N) (tn:treeNodes T≤N) (sn:treeNodes S≤N) (cap:EntryCap N e) :
 ∀F,(bothBadDispatchLocalSource actual T S e).value.answer=some F→
 F.length≤payloadSize N ∧ F.flatten.length≤payloadSize N := by
 intro F h
 have pl:=cap.1.1
 have mul:=Nat.mul_le_mul_left N pl
 have mul2:=Nat.mul_le_mul_left (2*N) pl
 have nn:1≤N:=by omega
 have grows:=Nat.mul_le_mul_left N nn
 cases hm:e.mode with
 | ordinary=>
   simp only [bothBadDispatchLocalSource,hm] at h
   have p:=ordinaryLocalSource_payload actual T S e.output.partition e.budget N three tn sn F h
   simp only [Nat.mul_assoc] at p mul mul2 grows ⊢
   simp only [payloadSize,Nat.mul_assoc] at *;omega
 | full=>
   simp only [bothBadDispatchLocalSource,hm] at h
   have p:=state_payload_forest_return actual (some T) _ e.budget F h
   have l:=Nat.le_trans (leaves_nodes T) tn
   dsimp only [StatePayloadSize,ForestState.labels] at p
   simp only [payloadSize,Nat.mul_assoc] at *;omega
 | retained parent residual completed known=>
   have m:ModeCap N (.retained parent residual completed known):=by rw [←hm];exact cap.2
   simp only [ModeCap] at m
   simp only [bothBadDispatchLocalSource,hm,retainedReconstructionMeter_value] at h
   cases ha:GenericForest.solve actual (localTargetMeter (some T) residual).value
     (ownedMeter (sourceForestMeter S e.output.partition).value residual).value e.budget with
   | none=>simp only [ha,Option.map_none] at h;cases h
   | some G=>
     have p:=callback_local_payload actual T residual _ e.budget N tn G ha
     have eq:known++G++[completed]=F:=by simpa only [ha,Option.map_some,Option.some.injEq] using h
     subst F
     simp only [List.length_append,List.length_cons,List.length_nil,List.flatten_append,
       List.flatten_cons,List.flatten_nil,List.append_nil]
     simp only [payloadSize,Nat.mul_assoc] at *;omega

/-- The envelope charges only this exact local source body. Forest callback
 computation remains in the unchanged callsForestDebit split. -/
theorem dispatch_bound (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree) (e : Entry) (N : Nat)
 (three:3≤N) (tn:treeNodes T≤N) (sn:treeNodes S≤N) (cap:EntryCap N e) :
 (bothBadDispatchLocalSource actual T S e).work≤dispatchPolynomial N ∧
 (bothBadDispatchLocalSource actual T S e).value.calls.length≤N := by
 have pl:=cap.1.1
 have material:=source_forest_work S e.output.partition N cap.1.2
 have scale:=Nat.mul_le_mul
   (Nat.add_le_add_right (Nat.mul_le_mul_left (4*(N+2)) sn) 3) cap.1.1
 have mc:(sourceForestMeter S e.output.partition).work≤materialPolynomial N:=by
   unfold materialPolynomial;omega
 cases hm:e.mode with
 | ordinary=>
   have w:=Nat.le_trans (ordinaryLocalSource_bound actual T S e.output.partition e.budget N three tn sn cap.1.2)
     (ordinaryPolynomial_mono N _ cap.1.1)
   have c:=ordinaryLocal_count actual T S e.output.partition e.budget
   simp only [bothBadDispatchLocalSource,hm,dispatchPolynomial];exact ⟨by omega,by omega⟩
 | full=>simp only [bothBadDispatchLocalSource,hm,dispatchPolynomial,List.length_cons,List.length_nil];exact ⟨by omega,by omega⟩
 | retained parent residual completed known=>
   have m:ModeCap N (.retained parent residual completed known):=by rw [←hm];exact cap.2
   simp only [ModeCap] at m
   have t:=localTargetMeter_bound T residual N tn (by omega)
   have count:=source_forest_count S e.output.partition
   have pl:=cap.1.1
   have nodes:∀s,s∈(sourceForestMeter S e.output.partition).value→treeNodes s≤N:=by
     intro s hs;exact Nat.le_trans (source_forest_payload S e.output.partition hs).1 sn
   have b:=ownedMeter_bound (sourceForestMeter S e.output.partition).value residual N nodes (by omega) (by omega)
   have f:=reconstruction_bound actual T residual (ownedMeter (sourceForestMeter S e.output.partition).value residual).value known completed e.budget N tn m.2.2.1
   simp only [bothBadDispatchLocalSource,hm,dispatchPolynomial,List.length_cons,List.length_nil]
   exact ⟨by omega,by omega⟩
end OrdinaryDispatch.Hard2SourceWork.LocalDispatchEnvelope
