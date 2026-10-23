import Hard2NonAdmittedExecutionV3

namespace SourceRule5CurrentV3
open RMAF ForestState Universal233 WholeSourceWork SourceForestV3
open Universal233.Rule5ExecutionSource
open GenericForest GenericForest.FrontierWork
open SourceCouplingV2 (Mode enabled)
open SourceDisjointV2 (ordinarySpec)

def hardReturn (T : Option Tree) (ss : List Tree) (out : SourceForestV3.Result) : CurrentReceipt :=
  ⟨.answered out.value,(forestPretestMeter T ss).work+3,out.debit,out.slots.map SourceCouplingV2.Slot.query⟩

inductive CurrentExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T : Option Tree) (ss : List Tree) (r k : Nat) : CurrentReceipt→List SourceForestV3.S→Prop
  | malformed (refused : (forestPretestMeter T ss).value=.refused) :
      CurrentExec OrdExec mode T ss r k ⟨.malformed,(forestPretestMeter T ss).work+2,0,[]⟩ []
  | found (pre : (forestPretestMeter T ss).value=.found F0) :
      CurrentExec OrdExec mode T ss r k
        ⟨.answered (if additionalCost ss F0≤r then some F0 else none),
          (forestPretestMeter T ss).work+F0.length+ss.length+4,0,[]⟩ []
  | low (pre : (forestPretestMeter T ss).value=.rejected) (low : r≤1) :
      CurrentExec OrdExec mode T ss r k ⟨.answered none,(forestPretestMeter T ss).work+3,0,[]⟩ []
  | hard (pre : (forestPretestMeter T ss).value=.rejected) (high : ¬r≤1)
      (forest : ForestExec OrdExec mode k T ss r out) :
      CurrentExec OrdExec mode T ss r k (hardReturn T ss out) out.slots

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F}

theorem current_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : CurrentExec OrdExec mode T ss r k result slots) :
    result=currentQueryMeter (ordinarySpec mode base) (fun _ _ _=>0) T ss r := by
  cases h with
  | malformed refused => simp only [currentQueryMeter,refused]
  | found pre => simp only [currentQueryMeter,pre]
  | low pre low => simp only [currentQueryMeter,pre,low,↓reduceIte]
  | hard pre high forest =>
    have hc:=forest_correspondence sound _ _ _ _ _ forest
    have hq:=SourceRule4V3.forest_slot_queries sound forest
    simp only [currentQueryMeter,pre,high,↓reduceIte,hardReturn,hc.1,hc.2.1,hq]

theorem current_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : CurrentExec OrdExec mode T ss r k result slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k result.ordinaryCalls := by
  cases h with
  | malformed refused => rfl
  | found pre => rfl
  | low pre low => rfl
  | hard pre high forest =>
    have hi:=(forest_correspondence sound _ _ _ _ _ forest).2.2
    have hq:=SourceRule4V3.forest_slot_queries sound forest
    simpa only [hardReturn,hq] using hi

theorem current_slots_realize (h : CurrentExec OrdExec mode T ss r k result slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | malformed refused => simp
  | found pre => simp
  | low pre low => simp
  | hard pre high forest => exact forest_slots_realize _ _ _ _ _ forest

theorem current_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T : Option Tree) (ss : List Tree) (r k : Nat) :
    ∃ result slots,CurrentExec OrdExec mode T ss r k result slots := by
  cases hp:(forestPretestMeter T ss).value with
  | refused => exact ⟨_,_,CurrentExec.malformed hp⟩
  | found F0 => exact ⟨_,_,CurrentExec.found hp⟩
  | rejected =>
    by_cases low:r≤1
    · exact ⟨_,_,CurrentExec.low hp low⟩
    · obtain ⟨out,forest⟩:=forest_exists total r k T ss
      exact ⟨_,_,CurrentExec.hard hp low forest⟩
end SourceRule5CurrentV3
