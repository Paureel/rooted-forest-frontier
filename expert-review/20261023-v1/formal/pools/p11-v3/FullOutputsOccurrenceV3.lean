import FullOutputsExecutionV3

namespace SourceFullOutputsV3
open RMAF Universal233 SourceForestV3 SourceCouplingV2
open OrdinaryDispatch.Hard2SourceWork

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem recorded_lower (h : OutputsExec OrdExec mode T S q i os r cells)
    (ls : (Nat×Nat)×SourceForestV3.S) (hs : ls∈recorded cells) : i≤ls.1.1 := by
  induction h with
  | nil => simp only [recorded,List.flatMap_nil,List.mem_nil_iff] at hs
  | refused tail over ih =>
    simp only [recorded,List.flatMap_cons,labelCell,cellSlots,List.map_nil,List.nil_append] at hs
    have ht:=ih hs; omega
  | returned tail paid execution ih =>
    change ls∈labelCell _++recorded _ at hs
    rcases List.mem_append.mp hs with hs|hs
    · simp only [labelCell,cellSlots] at hs
      obtain ⟨s,hslot,rfl⟩:=List.mem_map.mp hs
      exact Nat.le_refl _
    · have ht:=ih hs; omega

theorem recorded_distinct_ids
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : OutputsExec OrdExec mode T S q i os r cells) :
    (recorded cells).Pairwise (fun a b=>a.1≠b.1) := by
  induction h with
  | nil => simp [recorded]
  | refused tail over ih =>
    simpa only [recorded,List.flatMap_cons,labelCell,cellSlots,List.map_nil,List.nil_append] using ih
  | returned tail paid execution ih =>
    change (labelCell _++recorded _).Pairwise _
    rw [List.pairwise_append]
    refine ⟨?_,ih,?_⟩
    · have strict:=ledger_strict (forest_correspondence sound _ _ _ _ _ execution).2.2
      simp only [labelCell,cellSlots,List.pairwise_map]
      exact strict.imp (fun h he=>by have hz:=congrArg Prod.snd he; omega)
    · intro a ha b hb
      simp only [labelCell,cellSlots] at ha
      obtain ⟨s,hslot,rfl⟩:=List.mem_map.mp ha
      have hl:=recorded_lower tail b hb
      intro he
      have hz:=congrArg Prod.fst he
      dsimp at hz
      omega

theorem chronological_distinct_ids
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : OutputsExec OrdExec mode T S q i os r cells) :
    (chronological cells).Pairwise (fun a b=>a.1≠b.1) :=
  (two_ledger_perm cells).pairwise_iff (fun h=>Ne.symm h) |>.mpr (recorded_distinct_ids sound h)

def toRecorded (cells : List Cell) (x : {ls // ls∈chronological cells}) :
    {ls // ls∈recorded cells} := ⟨x.val,(two_ledger_perm cells).mem_iff.mp x.property⟩

def toChronological (cells : List Cell) (x : {ls // ls∈recorded cells}) :
    {ls // ls∈chronological cells} := ⟨x.val,(two_ledger_perm cells).mem_iff.mpr x.property⟩

theorem occurrence_left_inverse (cells : List Cell) (x : {ls // ls∈chronological cells}) :
    toChronological cells (toRecorded cells x)=x := rfl

theorem occurrence_right_inverse (cells : List Cell) (x : {ls // ls∈recorded cells}) :
    toRecorded cells (toChronological cells x)=x := rfl

def finishHard (T S : Tree) (q : Nat) (c : CherryBranching.Candidate) (out : Hard2Overlap.Result)
    (r : SourceExecution) : SourceExecution :=
  let os:=actualOutputsMeter S T c q out
  ⟨r.value,os.work+r.work+4⟩

inductive HardPaidExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T S : Tree) (q : Nat) (c : CherryBranching.Candidate) (out : Hard2Overlap.Result) :
    SourceExecution→List Cell→Prop
  | run (execution : OutputsExec OrdExec mode T S q 0 (actualOutputsMeter S T c q out).value r cells) :
      HardPaidExec OrdExec mode T S q c out (finishHard T S q c out r) cells

theorem hardPaid_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : HardPaidExec OrdExec mode T S q c out r cells) :
    r=hardPaidSource (SourceDisjointV2.ordinarySpec mode base) (fun _ _ _=>0) T S q c out := by
  cases h with
  | run execution =>
    have hr:=outputs_source_fields sound execution
    simp only [hardPaidSource,finishHard,hr]

end SourceFullOutputsV3
