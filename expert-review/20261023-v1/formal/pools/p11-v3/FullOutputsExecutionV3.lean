import SelectedChildrenConsumerV3

namespace SourceFullOutputsV3
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence GenericForest.FrontierWork
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration
open Universal233.Rule5SelectedLocalWork SourceForestV3 SourceCouplingV2
open SourceDisjointV2 (ordinarySpec)

structure Cell where
  outputIndex : Nat
  output : CoreProgram.Output
  result : Option SourceForestV3.Result

def callFor (T S : Tree) (q : Nat) (o : CoreProgram.Output) : BothBad.Call :=
  ⟨some T,(sourceForestMeter S o.partition).value,q-o.sourceCuts.length⟩

def cellSlots (c : Cell) : List SourceForestV3.S :=
  match c.result with | none=>[] | some out=>out.slots

def labelCell (c : Cell) : List ((Nat×Nat)×SourceForestV3.S) :=
  (cellSlots c).map (fun s=>((c.outputIndex,s.index),s))

def recorded (cells : List Cell) := cells.flatMap labelCell
def chronological (cells : List Cell) := cells.reverse.flatMap labelCell

def prependOutput (T S : Tree) (q : Nat) (o : CoreProgram.Output)
    (out : SourceForestV3.Result) (r : SourceExecution) : SourceExecution :=
  let ss:=sourceForestMeter S o.partition
  let c:=checkedMeter T S q out.value
  let b:=chooseMeter c.value r.value.answer
  ⟨⟨b.value,callFor T S q o::r.value.calls⟩,
    2*o.sourceCuts.length+ss.work+out.debit+c.work+b.work+r.work+14⟩

inductive OutputsExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T S : Tree) (q : Nat) : Nat→List CoreProgram.Output→SourceExecution→List Cell→Prop
  | nil : OutputsExec OrdExec mode T S q i [] ⟨⟨none,[]⟩,2⟩ []
  | refused (tail : OutputsExec OrdExec mode T S q (i+1) os r cells)
      (over : ¬o.sourceCuts.length≤q) :
      OutputsExec OrdExec mode T S q i (o::os)
        ⟨r.value,2*o.sourceCuts.length+r.work+6⟩ (⟨i,o,none⟩::cells)
  | returned (tail : OutputsExec OrdExec mode T S q (i+1) os r cells)
      (paid : o.sourceCuts.length≤q)
      (execution : ForestExec OrdExec mode 0 (some T) (sourceForestMeter S o.partition).value
        (q-o.sourceCuts.length) out) :
      OutputsExec OrdExec mode T S q i (o::os) (prependOutput T S q o out r)
        (⟨i,o,some out⟩::cells)

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem outputs_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : OutputsExec OrdExec mode T S q i os r cells) :
    r=fullOutputsSource (ordinarySpec mode base) (fun _ _ _=>0) T S q os := by
  induction h with
  | nil => rfl
  | refused tail over ih =>
    simp only [fullOutputsSource,over,↓reduceIte]
    rw [←ih]
  | returned tail paid execution ih =>
    have hc:=forest_correspondence sound _ _ _ _ _ execution
    simp only [fullOutputsSource,paid,↓reduceIte]
    rw [←ih,←hc.1,←hc.2.1]
    rfl

theorem outputs_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (q i : Nat) (os : List CoreProgram.Output) :
    ∃ r cells,OutputsExec OrdExec mode T S q i os r cells := by
  induction os generalizing i with
  | nil => exact ⟨_,_,OutputsExec.nil⟩
  | cons o os ih =>
    obtain ⟨r,cells,tail⟩:=ih (i+1)
    by_cases paid:o.sourceCuts.length≤q
    · obtain ⟨out,execution⟩:=forest_exists total (q-o.sourceCuts.length) 0 (some T)
        (sourceForestMeter S o.partition).value
      exact ⟨_,_,OutputsExec.returned tail paid execution⟩
    · exact ⟨_,_,OutputsExec.refused tail paid⟩

theorem output_ordinals (h : OutputsExec OrdExec mode T S q i os r cells) :
    cells.map (fun c=>(c.outputIndex,c.output))=CallbackPairingAuthor.indexFrom i os := by
  induction h with
  | nil => rfl
  | refused tail over ih =>
    simpa only [List.map_cons,CallbackPairingAuthor.indexFrom] using congrArg (List.cons _) ih
  | returned tail paid execution ih =>
    simpa only [List.map_cons,CallbackPairingAuthor.indexFrom] using congrArg (List.cons _) ih

theorem recorded_query_projection
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : OutputsExec OrdExec mode T S q i os r cells) :
    (recorded cells).map (fun ls=>ls.2.query)=forestQueries (ordinarySpec mode base) r.value.calls := by
  induction h with
  | nil => rfl
  | refused tail over ih =>
    simpa only [recorded,List.flatMap_cons,labelCell,cellSlots,List.map_nil,List.nil_append] using ih
  | returned tail paid execution ih =>
    have hq:=SourceRule4V3.forest_slot_queries sound execution
    simp only [recorded,forestQueries] at ih
    simp only [recorded,List.flatMap_cons,labelCell,cellSlots,List.map_append,List.map_map,
      Function.comp_def,prependOutput,forestQueries,List.flatMap_cons,callFor]
    rw [hq,ih]

theorem two_ledger_perm (cells : List Cell) : (chronological cells).Perm (recorded cells) :=
  (List.reverse_perm cells).flatMap_right labelCell

theorem two_ledger_sum (cells : List Cell) (fee : ((Nat×Nat)×SourceForestV3.S)→Nat) :
    ((chronological cells).map fee).sum=((recorded cells).map fee).sum :=
  ((two_ledger_perm cells).map fee).sum_nat

theorem chronological_cons (c : Cell) (cells : List Cell) :
    chronological (c::cells)=chronological cells++labelCell c := by
  simp only [chronological,List.reverse_cons,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]

theorem recorded_slots_realize
    (h : OutputsExec OrdExec mode T S q i os r cells) :
    ∀ ls∈recorded cells,SlotRealizes OrdExec mode ls.2 := by
  induction h with
  | nil => simp [recorded]
  | refused tail over ih =>
    simpa only [recorded,List.flatMap_cons,labelCell,cellSlots,List.map_nil,List.nil_append] using ih
  | returned tail paid execution ih =>
    intro ls hs
    change ls∈labelCell _++recorded _ at hs
    rcases List.mem_append.mp hs with hs|hs
    · simp only [labelCell,cellSlots] at hs
      obtain ⟨s,hslot,rfl⟩:=List.mem_map.mp hs
      exact forest_slots_realize _ _ _ _ _ execution s hslot
    · exact ih ls hs

theorem chronological_slots_realize
    (h : OutputsExec OrdExec mode T S q i os r cells) :
    ∀ ls∈chronological cells,SlotRealizes OrdExec mode ls.2 := by
  intro ls hs
  exact recorded_slots_realize h ls ((two_ledger_perm cells).mem_iff.mp hs)

end SourceFullOutputsV3
