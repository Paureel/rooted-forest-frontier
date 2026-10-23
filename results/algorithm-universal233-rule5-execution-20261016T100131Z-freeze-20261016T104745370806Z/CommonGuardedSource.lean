import CommonPaidBounds
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph Rule5PrefixLocalWork
open OrdinaryCommonSplit OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Source
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork
open WholeSourceWork CoreWork GenericForest.CheckCorrespondence

theorem outside_some (d : Setup) (FY : Forest) : ∃FN,outsideReply d FY=some FN := by
 cases hp:DepthOne.pretest01 d.myT d.myS with
 | found c=>exact ⟨DepthOne.forest d.myS c,by simp [outsideReply,hp]⟩
 | rejected=>exact ⟨outsideExtension d FY,by simp [outsideReply,hp]⟩
 | refused=>
  have bad:=(DepthOne.refused_iff d.myT d.myS).1 hp
  have good:=marked_outside_proper d
  simp [good] at bad

def withOutsideMeter (cb : Ordinary) (W : OrdinaryWork) (d : Setup) (q : Nat) (FY : Forest) : CommonReceipt (Option Forest) :=
 let out:=outsideReplyMeter d FY
 match out.value with
 | none=>⟨none,out.work+2,0,[]⟩
 | some FN=>let r:=runPaidMeter cb W d q FY FN
            ⟨r.value,out.work+r.localWork+2,r.recursiveWork,r.calls⟩

theorem with_outside_value (cb : Ordinary) (W : OrdinaryWork) (d : Setup) (q : Nat) (FY : Forest) :
 (withOutsideMeter cb W d q FY).value=runWithOutside d q FY cb := by
 simp only [withOutsideMeter,outside_reply_value,runWithOutside,run_paid_value]
 split <;> simp_all

theorem with_outside_calls (cb : Ordinary) (W : OrdinaryWork) (d : Setup) (q : Nat) (FY : Forest) :
 (withOutsideMeter cb W d q FY).calls=paidJobs d q := by
 obtain ⟨FN,answer⟩:=outside_some d FY
 simp only [withOutsideMeter,outside_reply_value,answer,run_paid_calls]

theorem with_outside_recursive (cb : Ordinary) (W : OrdinaryWork) (d : Setup) (q : Nat) (FY : Forest) :
 (withOutsideMeter cb W d q FY).recursiveWork=
 (((withOutsideMeter cb W d q FY).calls).map (fun j=>W j.T j.S j.budget)).sum := by
 simp only [withOutsideMeter]
 split
 · rfl
 · rename_i FN hfn
   exact run_paid_recursive cb W d q FY FN

def guardedMeter (cb : Ordinary) (W : OrdinaryWork) (d : Setup) (q : Nat) : CommonReceipt (Option (Option Forest)) :=
 let pre:=meterPretest d.ty d.sy
 match pre.value with
 | .found (some p)=>
   let fy:=meterForest d.sy (some p)
   let r:=withOutsideMeter cb W d q fy.value
   ⟨some r.value,pre.work+fy.work+r.localWork+3,r.recursiveWork,r.calls⟩
 | _=>⟨none,pre.work+2,0,[]⟩

theorem guarded_value (cb : Ordinary) (W : OrdinaryWork) (d : Setup) (q : Nat) :
 (guardedMeter cb W d q).value=runGuarded d q cb := by
 simp only [guardedMeter,meterPretest_value,meterForest_value,with_outside_value,runGuarded]
 split <;> simp_all

theorem guarded_calls (cb : Ordinary) (W : OrdinaryWork) (d : Setup) (q : Nat) :
 (guardedMeter cb W d q).calls=guardedJobs d q := by
 simp only [guardedMeter,meterPretest_value,with_outside_calls,guardedJobs]
 split <;> simp_all

theorem guarded_recursive (cb : Ordinary) (W : OrdinaryWork) (d : Setup) (q : Nat) :
 (guardedMeter cb W d q).recursiveWork=
 (((guardedMeter cb W d q).calls).map (fun j=>W j.T j.S j.budget)).sum := by
 simp only [guardedMeter]
 split
 · exact with_outside_recursive _ _ _ _ _
 · rfl

theorem setup_pretest_nodes (d : Setup) :
 treeNodes d.ty≤2*(leaves d.T).length ∧ treeNodes d.sy≤2*(leaves d.T).length ∧
 treeNodes d.myT≤2*(leaves d.T).length ∧ treeNodes d.myS≤2*(leaves d.T).length := by
 have caps:=setup_tree_node_caps d
 have ty:=Rule5ActualTrace.restricted_size d.nt d.hty
 have sy:=Rule5ActualTrace.restricted_size d.ns d.hsy
 have myT:=Rule5ActualTrace.marked_size d.nt d.hMYT
 have myS:=Rule5ActualTrace.marked_size d.ns d.hMYS
 have tn:=treeNodes_leafCount d.T;have sn:=treeNodes_leafCount d.S
 have yn:=treeNodes_leafCount d.ty;have zn:=treeNodes_leafCount d.sy
 have mn:=treeNodes_leafCount d.myT;have nn:=treeNodes_leafCount d.myS
 exact ⟨by omega,by omega,by omega,by omega⟩

def guardedBudget (n : Nat) :=400000*(2*n+1)^6+128*(2*n+1)^3+
 outsideBudget (2*n) (4*n+2)+paidBudget n+8

theorem guarded_local (W : OrdinaryWork) (d : Setup) (q : Nat) :
 (guardedMeter Rule5LocalWork.actual W d q).localWork≤guardedBudget (leaves d.T).length := by
 have caps:=setup_pretest_nodes d
 have pre:=meterPretest_bound d.ty d.sy (2*(leaves d.T).length) caps.1 caps.2.1
 simp only [guardedMeter]
 split
 · rename_i p hp
   have hp' : DepthOne.pretest01 d.ty d.sy=.found (some p):=by simpa only [meterPretest_value] using hp
   have cp:=pretest_candidate d.ty d.sy hp'
   have fywork:=meterForest_bound d.sy (some p) (2*(leaves d.T).length) caps.2.1
    (fun v hv=>Nat.le_trans (candidate_address d.sy (some p) cp v hv) caps.2.1)
   have pay:=forest_cells d.sy (some p)
   have fycells : Rule5LocalWork.cells (meterForest d.sy (some p)).value≤4*(leaves d.T).length+2 := by
    simp only [meterForest_value,Rule5LocalWork.cells];omega
   have out:=outside_reply_work d (meterForest d.sy (some p)).value (2*(leaves d.T).length) (4*(leaves d.T).length+2) caps.2.2.1 caps.2.2.2 fycells
   simp only [withOutsideMeter]
   split
   · unfold guardedBudget;dsimp only;omega
   · rename_i FN hfn
     have paid:=run_paid_local W d q (FY:=(meterForest d.sy (some p)).value) (FN:=FN) hp' (meterForest_value d.sy (some p)) (by simpa only [outside_reply_value] using hfn)
     unfold guardedBudget;dsimp only;omega
 · unfold guardedBudget;dsimp only;omega
end Universal233.Rule5ExecutionSource
