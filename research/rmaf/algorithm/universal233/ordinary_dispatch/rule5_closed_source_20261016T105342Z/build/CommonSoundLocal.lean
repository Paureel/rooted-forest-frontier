import CommonCutoffPayload
namespace Universal233.Rule5ClosedSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5ExecutionSource
open OrdinaryCommonSplit OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Source
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.FastOrdinary
open WholeSourceWork CoreWork GenericForest.CheckCorrespondence
open Rule5RemainingLocalWork Rule5PendantLocalWork Rule5FinalClassification Rule5Classification Rule5Local Rule5CommonSelector
theorem run_paid_sound_local (cb : Ordinary) (sound : CallbackSound cb) (W : OrdinaryWork) (d : Setup) (q : Nat) {FY FN : Forest} {p : RMAF.Vertex}
 (pre : DepthOne.pretest01 d.ty d.sy=.found (some p))
 (fy : FY=DepthOne.forest d.sy (some p)) (fn : outsideReply d FY=some FN) :
 (runPaidMeter cb W d q FY FN).localWork≤paidBudget (leaves d.T).length := by
 by_cases zero:q=0
 · subst q
   simp only [runPaidMeter,paidJobsMeter,↓reduceIte,jobsAnswersMeter]
   unfold paidBudget;(try dsimp only);omega
 · have js : (paidJobsMeter d q).value=[⟨d.tx,d.sx,q-1⟩,⟨d.mxT,d.mxS,q-1⟩] := by simp [paidJobsMeter,zero]
   have jw : (paidJobsMeter d q).work=12 := by simp [paidJobsMeter,zero]
   cases fx:cb d.tx d.sx (q-1) with
   | none=>simp only [runPaidMeter,js,jw,jobsAnswersMeter,fx];unfold paidBudget;(try dsimp only);omega
   | some FX=>
    cases fm:cb d.mxT d.mxS (q-1) with
    | none=>simp only [runPaidMeter,js,jw,jobsAnswersMeter,fx,fm];unfold paidBudget;(try dsimp only);omega
    | some FM=>
     have recon:=common_sound_reconstruct_work cb sound d (q-1) fx fm pre fy fn
     have pay:=common_sound_payloads cb sound d (q-1) fx fm pre fy fn
     simp only [runPaidMeter,js,jw,jobsAnswersMeter,fx,fm]
     split
     · unfold paidBudget;(try dsimp only);omega
     · rename_i G hg
       have len:=reconstruct_length d FX FY FM FN (2*(leaves d.T).length) pay.1 pay.2.1 pay.2.2.1 pay.2.2.2
        (by rw [←reconstruct_actual_agreement];exact hg)
       unfold paidBudget;(try dsimp only);omega
theorem guarded_sound_local (cb : Ordinary) (sound : CallbackSound cb) (W : OrdinaryWork) (d : Setup) (q : Nat) :
 (guardedMeter cb W d q).localWork≤guardedBudget (leaves d.T).length := by
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
     have paid:=run_paid_sound_local cb sound W d q (FY:=(meterForest d.sy (some p)).value) (FN:=FN) hp' (meterForest_value d.sy (some p)) (by simpa only [outside_reply_value] using hfn)
     unfold guardedBudget;dsimp only;omega
 · unfold guardedBudget;dsimp only;omega
theorem common_sound_local (cb : Ordinary) (sound : CallbackSound cb) (classFee : CheckRequest→Nat) (W : OrdinaryWork) {T S : Tree} {i e : RMAF.Vertex}
 {a b : Nat} {d : BadSelection} (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (sel : (finalMeter classFee T S a b).value=some (.remaining d (.one e))) (q : Nat) :
 (commonMeter cb W T S a b d q).localWork≤commonBudget (leaves T).length (leaves S).length (subtreeLabels S d.badArc).length := by
 have setup:=common_setup_work classFee ch ad sel
 simp only [commonMeter]
 split
 · unfold commonBudget;dsimp only;omega
 · rename_i built hb
   have original : buildSetup T S (subtreeLabels S d.badArc) (outsideLabels S a b d) d.badArc=some built := by
    simpa only [common_setup_value] using hb
   have ident:=buildSetup_identity T S _ _ _ built original
   have r:=guarded_sound_local cb sound W built q
   rw [ident.1] at r
   unfold commonBudget;dsimp only;omega


theorem common_sound_source_local (cb : Ordinary) (sound : CallbackSound cb) (classFee : CheckRequest→Nat)
 {T S : Tree} {i e : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch:CherryAt T i a b) (ad:admitted T S a b=true)
 (sel:(finalMeter classFee T S a b).value=some (.remaining d (.one e))) (q : Nat) :
 (commonSource cb (fun _ _ _=>0) T S a b d q).work≤commonBudget (leaves T).length (leaves S).length (subtreeLabels S d.badArc).length := by
 have bound:=common_sound_local cb sound classFee (fun _ _ _=>0) ch ad sel q
 have zero:(commonMeter cb (fun _ _ _=>0) T S a b d q).recursiveWork=0:=by rw [common_recursive,map_zero_sum]
 simpa only [commonSource,zero,Nat.add_zero] using bound
end Universal233.Rule5ClosedSource
