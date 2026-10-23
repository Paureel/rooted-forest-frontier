import CommonExecutionV3
import Rule4CallerSource

namespace SourceRule4V3
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence GenericForest.FrontierWork
open OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion
open SourceForestV3 SourceCouplingV2
open SourceDisjointV2 (ordinarySpec)
open CallbackPairingAuthor (indexFrom)

structure Cell where
  branchIndex : Nat
  branch : Rule4.Branch
  state : Charged (List Tree)
  result : Option SourceForestV3.Result

def cellSlots (cell : Cell) : List SourceForestV3.S :=
  match cell.result with | none=>[] | some out=>out.slots

def labelCell (cell : Cell) : List ((Nat×Nat)×SourceForestV3.S) :=
  (cellSlots cell).map fun s=>((cell.branchIndex,s.index),s)

def recorded (cells : List Cell) : List ((Nat×Nat)×SourceForestV3.S) :=
  cells.flatMap labelCell

def chronological (cells : List Cell) : List ((Nat×Nat)×SourceForestV3.S) :=
  cells.reverse.flatMap labelCell

-- The state field remains in every refused cell even though the literal source
-- returned work omits state.work on that branch. This is an open count credit.
def refusedStateWork (cells : List Cell) : Nat :=
  (cells.map fun c=>if c.result.isNone then c.state.work else 0).sum

-- Tail is the first execution premise, then the unconditionally built state,
-- then the affordable forest. Cell order is separately the recorded head order.
inductive AnswersExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode) (q : Nat) :
    Nat→List Rule4.Branch→Charged (List F)→List Cell→Prop
  | nil : AnswersExec OrdExec mode q i [] ⟨[],1⟩ []
  | refused (tail : AnswersExec OrdExec mode q (i+1) bs r cells)
      (over : ¬b.cost≤q) :
      AnswersExec OrdExec mode q i (b::bs)
        ⟨r.value,2*b.cuts.length+4+r.work⟩
        (⟨i,b,rule4StateMeter b,none⟩::cells)
  | returned (tail : AnswersExec OrdExec mode q (i+1) bs r cells)
      (paid : b.cost≤q)
      (execution : ForestExec OrdExec mode 0 (some b.target) (rule4StateMeter b).value (q-b.cost) out) :
      AnswersExec OrdExec mode q i (b::bs)
        ⟨out.value.toList++r.value,
          (rule4StateMeter b).work+2*b.cuts.length+8+out.debit+r.work⟩
        (⟨i,b,rule4StateMeter b,some out⟩::cells)

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F}

theorem answers_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : AnswersExec OrdExec mode q i bs r cells) :
    r=rule4AnswersSource (ordinarySpec mode base) (fun _ _ _=>0) q bs := by
  induction h with
  | nil => rfl
  | refused tail over ih =>
    simp only [rule4AnswersSource,over,↓reduceIte]
    rw [←ih]
  | returned tail paid execution ih =>
    have hc:=forest_correspondence sound _ _ _ _ _ execution
    simp only [rule4AnswersSource,paid,↓reduceIte]
    rw [←ih,←hc.1,←hc.2.1]

theorem answers_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (q i : Nat) (bs : List Rule4.Branch) :
    ∃ r cells,AnswersExec OrdExec mode q i bs r cells := by
  induction bs generalizing i with
  | nil => exact ⟨_,_,AnswersExec.nil⟩
  | cons b bs ih =>
    obtain ⟨r,cells,tail⟩:=ih (i+1)
    by_cases paid:b.cost≤q
    · obtain ⟨out,execution⟩:=forest_exists total (q-b.cost) 0 (some b.target) (rule4StateMeter b).value
      exact ⟨_,_,AnswersExec.returned tail paid execution⟩
    · exact ⟨_,_,AnswersExec.refused tail paid⟩

theorem cells_branches (h : AnswersExec OrdExec mode q i bs r cells) :
    cells.map (fun c=>(c.branchIndex,c.branch))=indexFrom i bs := by
  induction h with
  | nil => rfl
  | refused tail over ih => simpa only [List.map_cons,indexFrom] using congrArg (List.cons _) ih
  | returned tail paid execution ih => simpa only [List.map_cons,indexFrom] using congrArg (List.cons _) ih

theorem cells_realize (h : AnswersExec OrdExec mode q i bs r cells) :
    ∀ c∈cells,c.state=rule4StateMeter c.branch ∧
      (match c.result with
      | none=>¬c.branch.cost≤q
      | some out=>c.branch.cost≤q ∧ ForestExec OrdExec mode 0 (some c.branch.target)
          c.state.value (q-c.branch.cost) out) := by
  induction h with
  | nil => simp
  | refused tail over ih =>
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl|hc
    · exact ⟨rfl,over⟩
    · exact ih c hc
  | returned tail paid execution ih =>
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl|hc
    · exact ⟨rfl,paid,execution⟩
    · exact ih c hc

theorem two_ledger_perm (cells : List Cell) : (chronological cells).Perm (recorded cells) := by
  exact (List.reverse_perm cells).flatMap_right labelCell

theorem two_ledger_sum (cells : List Cell) (fee : ((Nat×Nat)×SourceForestV3.S)→Nat) :
    ((chronological cells).map fee).sum=((recorded cells).map fee).sum := by
  exact ((two_ledger_perm cells).map fee).sum_nat

theorem chronological_cons (c : Cell) (cells : List Cell) :
    chronological (c::cells)=chronological cells++labelCell c := by
  simp only [chronological,List.reverse_cons,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]

theorem recorded_slots_realize
    (h : AnswersExec OrdExec mode q i bs r cells) :
    ∀ ls∈recorded cells,SlotRealizes OrdExec mode ls.2 := by
  intro ls hs
  change ls∈cells.flatMap labelCell at hs
  obtain ⟨c,hc,hls⟩:=List.mem_flatMap.mp hs
  change ls∈(cellSlots c).map (fun s=>((c.branchIndex,s.index),s)) at hls
  obtain ⟨s,hslot,rfl⟩:=List.mem_map.mp hls
  have hr:=cells_realize h c hc
  cases he:c.result with
  | none => simp only [cellSlots,he,List.mem_nil_iff] at hslot
  | some out =>
    simp only [he] at hr
    simp only [cellSlots,he] at hslot
    exact forest_slots_realize _ _ _ _ _ hr.2.2 s hslot

theorem chronological_slots_realize
    (h : AnswersExec OrdExec mode q i bs r cells) :
    ∀ ls∈chronological cells,SlotRealizes OrdExec mode ls.2 := by
  intro ls hs
  exact recorded_slots_realize h ls ((two_ledger_perm cells).mem_iff.mp hs)

end SourceRule4V3
