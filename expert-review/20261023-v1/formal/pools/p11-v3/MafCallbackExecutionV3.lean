import GoodPairExecutionV3

namespace SourceMafCallbackV3
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence GenericForest.FrontierWork
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration
open SourceForestV3 SourceCouplingV2
open SourceDisjointV2 (ordinarySpec)

structure Return where
  meter : Charged (Option (Nat×F))
  calls : List BothBad.Call
  debits : List Nat
  slots : List SourceForestV3.S

def request (T S : Tree) (U : List Nat) (b : Nat) : Option BothBad.Call :=
  match (meterRestrict U T).value,(meterRestrict U S).value with
  | some t,some s=>some ⟨some t,[s],b⟩
  | _,_=>none

def missingReturn (T S : Tree) (U : List Nat) : Return :=
  ⟨⟨none,(meterRestrict U T).work+(meterRestrict U S).work+8⟩,[],[],[]⟩

def forestReturn (T S : Tree) (U : List Nat) (b : Nat) (t s : Tree)
    (out : SourceForestV3.Result) : Return :=
  ⟨⟨out.value.map (fun F=>(F.length-1,F)),
      (meterRestrict U T).work+(meterRestrict U S).work+(out.value.map List.length).getD 0+12⟩,
    [⟨some t,[s],b⟩],[out.debit],out.slots⟩

inductive MafExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T S : Tree) (U : List Nat) (b k : Nat) : Return→Prop
  | missing (absent : (meterRestrict U T).value=none ∨ (meterRestrict U S).value=none) :
      MafExec OrdExec mode T S U b k (missingReturn T S U)
  | returned (left : (meterRestrict U T).value=some t) (right : (meterRestrict U S).value=some s)
      (execution : ForestExec OrdExec mode k (some t) [s] b out) :
      MafExec OrdExec mode T S U b k (forestReturn T S U b t s out)

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem maf_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : MafExec OrdExec mode T S U b k ret) :
    ret.meter=mafRecursiveMeter (ordinarySpec mode base) T S U b := by
  cases h with
  | missing absent =>
    rcases absent with left|right
    · simp only [mafRecursiveMeter,left,missingReturn]
    · cases ht:(meterRestrict U T).value <;> simp only [mafRecursiveMeter,ht,right,missingReturn]
  | returned left right execution =>
    have hv:=(forest_correspondence sound _ _ _ _ _ execution).1
    simp only [mafRecursiveMeter,left,right,forestReturn,←hv]

theorem maf_calls (h : MafExec OrdExec mode T S U b k ret) : ret.calls=(request T S U b).toList := by
  cases h with
  | missing absent =>
    rcases absent with left|right
    · simp only [request,left,missingReturn,Option.toList_none]
    · cases ht:(meterRestrict U T).value <;> simp only [request,ht,right,missingReturn,Option.toList_none]
  | returned left right execution => simp only [forestReturn,request,left,right,Option.toList_some]

theorem maf_debits
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : MafExec OrdExec mode T S U b k ret) :
    ret.debits.sum=callsForestDebit (ordinarySpec mode base) (fun _ _ _=>0) ret.calls := by
  cases h with
  | missing absent => rfl
  | returned left right execution =>
    have hd:=(forest_correspondence sound _ _ _ _ _ execution).2.1
    simp only [forestReturn,callsForestDebit,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,hd]

theorem maf_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : MafExec OrdExec mode T S U b k ret) :
    ret.slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (forestQueries (ordinarySpec mode base) ret.calls) := by
  cases h with
  | missing absent => rfl
  | returned left right execution =>
    simpa only [forestReturn,forestQueries,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
      (forest_correspondence sound _ _ _ _ _ execution).2.2

theorem maf_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (U : List Nat) (b k : Nat) : ∃ ret,MafExec OrdExec mode T S U b k ret := by
  cases ht:(meterRestrict U T).value with
  | none => exact ⟨_,MafExec.missing (Or.inl ht)⟩
  | some t =>
    cases hs:(meterRestrict U S).value with
    | none => exact ⟨_,MafExec.missing (Or.inr hs)⟩
    | some s =>
      obtain ⟨out,execution⟩:=forest_exists total b k (some t) [s]
      exact ⟨_,MafExec.returned ht hs execution⟩

end SourceMafCallbackV3
