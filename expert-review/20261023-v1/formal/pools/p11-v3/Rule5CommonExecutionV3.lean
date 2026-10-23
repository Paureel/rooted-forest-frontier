import Rule5CommonJobsV3

namespace SourceRule5CommonV3
open RMAF Universal233 WholeSourceWork CoreWork SourceForestV3
open Universal233.Rule5ExecutionSource Universal233.Rule5RemainingLocalWork
open OrdinaryCommonSplit.Caller GenericForest.CheckCorrespondence
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork
open SourceCouplingV2 (Mode enabled)
open SourceDisjointV2 (ordinarySpec)

def reconstruction (d : Setup) (q : Nat) (FY FN : F) (asw : List (Option F)) : Charged (Option F) :=
  match asw with
  | [some FX,some FM]=>
    let r:=Rule5LocalWork.reconstructMeter (measuredAgreement d.T d.S) d FX FY FM FN
    match r.value with
    | none=>⟨none,r.work+2⟩
    | some G=>⟨if G.length-1≤q then some G else none,r.work+G.length+4⟩
  | _=>⟨none,2⟩

def paidReturn (d : Setup) (q : Nat) (FY FN : F) (asw : CommonReceipt (List (Option F))) : CommonReceipt (Option F) :=
  let js:=paidJobsMeter d q
  let final:=reconstruction d q FY FN asw.value
  ⟨final.value,js.work+asw.localWork+final.work+2,asw.recursiveWork,asw.calls⟩

inductive PaidExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (d : Setup) (q k : Nat) (FY FN : F) : CommonReceipt (Option F)→List SourceForestV3.S→Prop
  | run (jobs : SourceRule5CommonJobsV3.JobsExec OrdExec mode k (paidJobsMeter d q).value asw slots) :
      PaidExec OrdExec mode d q k FY FN (paidReturn d q FY FN asw) slots

def outsideReturn (d : Setup) (FY : F) (r : CommonReceipt (Option F)) : CommonReceipt (Option F) :=
  ⟨r.value,(outsideReplyMeter d FY).work+r.localWork+2,r.recursiveWork,r.calls⟩
inductive OutsideExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (d : Setup) (q k : Nat) (FY : F) : CommonReceipt (Option F)→List SourceForestV3.S→Prop
  | refused (empty : (outsideReplyMeter d FY).value=none) :
      OutsideExec OrdExec mode d q k FY ⟨none,(outsideReplyMeter d FY).work+2,0,[]⟩ []
  | paid (found : (outsideReplyMeter d FY).value=some FN) (execution : PaidExec OrdExec mode d q k FY FN r slots) :
      OutsideExec OrdExec mode d q k FY (outsideReturn d FY r) slots

def guardedReturn (d : Setup) (p : Vertex) (r : CommonReceipt (Option F)) : CommonReceipt (Option (Option F)) :=
  let pre:=meterPretest d.ty d.sy
  let fy:=meterForest d.sy (some p)
  ⟨some r.value,pre.work+fy.work+r.localWork+3,r.recursiveWork,r.calls⟩
inductive GuardedExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (d : Setup) (q k : Nat) : CommonReceipt (Option (Option F))→List SourceForestV3.S→Prop
  | refused (empty : ¬∃ p,(meterPretest d.ty d.sy).value=.found (some p)) :
      GuardedExec OrdExec mode d q k ⟨none,(meterPretest d.ty d.sy).work+2,0,[]⟩ []
  | found (selected : (meterPretest d.ty d.sy).value=.found (some p))
      (execution : OutsideExec OrdExec mode d q k (meterForest d.sy (some p)).value r slots) :
      GuardedExec OrdExec mode d q k (guardedReturn d p r) slots

def commonReturn (T S : Tree) (a b : Nat) (d : Rule5FinalClassification.BadSelection)
    (r : CommonReceipt (Option (Option F))) : CommonReceipt (Option F) :=
  ⟨r.value.join,(commonSetupMeter T S a b d).work+r.localWork+3,r.recursiveWork,r.calls⟩
inductive CommonExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T S : Tree) (a b q k : Nat) (d : Rule5FinalClassification.BadSelection) :
    CommonReceipt (Option F)→List SourceForestV3.S→Prop
  | refused (empty : (commonSetupMeter T S a b d).value=none) :
      CommonExec OrdExec mode T S a b q k d ⟨none,(commonSetupMeter T S a b d).work+2,0,[]⟩ []
  | built (found : (commonSetupMeter T S a b d).value=some setup)
      (execution : GuardedExec OrdExec mode setup q k r slots) :
      CommonExec OrdExec mode T S a b q k d (commonReturn T S a b d r) slots

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem paid_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : PaidExec OrdExec mode d q k FY FN r slots) :
    r=runPaidMeter (ordinarySpec mode base) (fun _ _ _=>0) d q FY FN := by
  cases h with
  | run jobs =>
    have hv:=SourceRule5CommonJobsV3.jobs_source_fields sound jobs
    simp only [paidReturn,runPaidMeter,reconstruction,hv]
    rfl

theorem outside_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : OutsideExec OrdExec mode d q k FY r slots) :
    r=withOutsideMeter (ordinarySpec mode base) (fun _ _ _=>0) d q FY := by
  cases h with
  | refused empty => simp only [withOutsideMeter,empty]
  | paid found execution =>
    have hv:=paid_source_fields sound execution
    simp only [withOutsideMeter,found,outsideReturn,hv]

theorem guarded_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : GuardedExec OrdExec mode d q k r slots) :
    r=guardedMeter (ordinarySpec mode base) (fun _ _ _=>0) d q := by
  cases h with
  | refused empty =>
    cases hp:(meterPretest d.ty d.sy).value with
    | refused => simp only [guardedMeter,hp]
    | rejected => simp only [guardedMeter,hp]
    | found pair =>
      cases pair with
      | none => simp only [guardedMeter,hp]
      | some p => exact False.elim (empty ⟨p,hp⟩)
  | found selected execution =>
    have hv:=outside_source_fields sound execution
    simp only [guardedMeter,selected,guardedReturn,hv]

theorem common_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : CommonExec OrdExec mode T S a b q k d r slots) :
    r=commonMeter (ordinarySpec mode base) (fun _ _ _=>0) T S a b d q := by
  cases h with
  | refused empty => simp only [commonMeter,empty]
  | built found execution =>
    have hv:=guarded_source_fields sound execution
    simp only [commonMeter,found,commonReturn,hv]

def sourceView (r : CommonReceipt (Option F)) : Charged (Option F) :=
  ⟨r.value,r.localWork+r.recursiveWork⟩
theorem common_source_view
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : CommonExec OrdExec mode T S a b q k d r slots) :
    sourceView r=commonSource (ordinarySpec mode base) (fun _ _ _=>0) T S a b d q := by
  simp only [sourceView,commonSource,←common_source_fields sound h]
end SourceRule5CommonV3
