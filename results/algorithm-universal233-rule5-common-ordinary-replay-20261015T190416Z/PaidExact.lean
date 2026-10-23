import InsideBudget
namespace OrdinaryCommonSplit.Caller
open RMAF

/-- Conditional exactness at the actual two listed q-1 callback invocations.
The outside minimum one and its actual replies remain explicit consuming
inputs; deriving them from admitted source Rule5 geometry is still OPEN. -/
theorem runPaid_exact (d : Setup) (q : Nat) (FY FN : Forest)
    (cb : Tree→Tree→Nat→Option Forest)
    (aFY : agreement d.ty d.sy FY=true) (cFY : FY.length-1=1)
    (hn : IsMinimum d.ty d.sy 1)
    (aFN : agreement d.myT d.myS FN=true)
    (hg : IsMinimum d.myT d.myS (FN.length-1))
    (ih : ActualIH d q cb) : BoundedExact d.T d.S q (runPaid d q FY FN cb) := by
  by_cases zero : q=0
  · subst q
    simp only [runPaid,paidJobs,ite_eq_left rfl,List.map_nil,BoundedExact]
    intro F aF
    have debt := (ordinary_inside_debt d hn F aF).2
    omega
  · have ordinaryIH := ih ⟨d.tx,d.sx,q-1⟩ (by simp [paidJobs,zero])
    have markedIH := ih ⟨d.mxT,d.mxS,q-1⟩ (by simp [paidJobs,zero])
    cases hOrd : cb d.tx d.sx (q-1) with
    | none =>
      have noOrd : ∀G,agreement d.tx d.sx G=true→q-1<G.length-1 := by
        simpa only [hOrd,BoundedExact] using ordinaryIH
      have run : runPaid d q FY FN cb=none := by simp [runPaid,paidJobs,zero,hOrd]
      rw [run]
      intro F aF
      obtain ⟨aX,debt⟩ := ordinary_inside_debt d hn F aF
      have no := noOrd _ aX
      omega
    | some FX =>
      have sOrd : agreement d.tx d.sx FX=true ∧ FX.length-1≤q-1 ∧
          ∀H,agreement d.tx d.sx H=true→FX.length-1≤H.length-1 := by
        simpa only [hOrd,BoundedExact] using ordinaryIH
      have hm : IsMinimum d.tx d.sx (FX.length-1) := ⟨⟨FX,sOrd.1,rfl⟩,sOrd.2.2⟩
      cases hMark : cb d.mxT d.mxS (q-1) with
      | none =>
        have noMark : ∀G,agreement d.mxT d.mxS G=true→q-1<G.length-1 := by
          simpa only [hMark,BoundedExact] using markedIH
        have run : runPaid d q FY FN cb=none := by simp [runPaid,paidJobs,zero,hOrd,hMark]
        rw [run]
        intro F aF
        by_cases fits : F.length-1≤q
        · obtain ⟨G,aG,cG⟩ := marked_inside_feasible d _ q hm hn F aF fits
          have no := noMark G aG
          omega
        · omega
      | some FM =>
        have sMark : agreement d.mxT d.mxS FM=true ∧ FM.length-1≤q-1 ∧
            ∀H,agreement d.mxT d.mxS H=true→FM.length-1≤H.length-1 := by
          simpa only [hMark,BoundedExact] using markedIH
        have hr : IsMinimum d.mxT d.mxS (FM.length-1) := ⟨⟨FM,sMark.1,rfl⟩,sMark.2.2⟩
        have hn' : IsMinimum d.ty d.sy (FY.length-1) := cFY.symm ▸ hn
        obtain ⟨G,hG,aG,cG,minG⟩ := reconstruct_actual_spec d FX FY FM FN
          sOrd.1 aFY sMark.1 aFN hm hn' hr hg
        by_cases fit : G.length-1≤q
        · have run : runPaid d q FY FN cb=some G := by simp [runPaid,paidJobs,zero,hOrd,hMark,hG,fit]
          rw [run]
          exact ⟨aG,fit,minG⟩
        · have run : runPaid d q FY FN cb=none := by simp [runPaid,paidJobs,zero,hOrd,hMark,hG,fit]
          rw [run]
          intro F aF
          have bound := minG F aF
          omega
end OrdinaryCommonSplit.Caller
