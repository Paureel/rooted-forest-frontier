import SlotRealizationV3
import CommonBranchWork

namespace SourceCommonV3
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence GenericForest.FrontierWork
open OrdinaryDispatch.FullSourceWork SourceForestV3 SourceCouplingV2

def pair (T S : Tree) (reverse : Bool) (c : CherryBranching.Candidate) : Tree×Tree :=
  (commonPairMeter T S reverse c).value

def smaller (T S : Tree) (reverse : Bool) (c : CherryBranching.Candidate) : Prop :=
  (meterLeaves (pair T S reverse c).1).value.length<(meterLeaves T).value.length
instance (T S : Tree) (reverse : Bool) (c : CherryBranching.Candidate) :
    Decidable (smaller T S reverse c) := inferInstanceAs (Decidable (_<_))

def returned (T S : Tree) (reverse : Bool) (c : CherryBranching.Candidate)
    (answer : Option F) : Charged (Option F) :=
  let p:=commonPairMeter T S reverse c
  let a:=meterLeaves p.value.1
  let b:=meterLeaves T
  match answer with
  | none=>⟨none,p.work+a.work+b.work+0+8⟩
  | some fs=>let e:=expandCommonMeter T S reverse c fs
             ⟨some e.value,p.work+a.work+b.work+0+e.work+8⟩

def refused (T S : Tree) (reverse : Bool) (c : CherryBranching.Candidate) : Charged (Option F) :=
  let p:=commonPairMeter T S reverse c
  let a:=meterLeaves p.value.1
  let b:=meterLeaves T
  ⟨none,p.work+a.work+b.work+4⟩

inductive CommonExec (OrdExec : Tree→Tree→Nat→Option F→Prop)
    (q : Nat) (T S : Tree) (reverse : Bool) (c : CherryBranching.Candidate) (k : Nat) :
    Charged (Option F)→List SourceForestV3.S→Prop
  | refused (large : ¬smaller T S reverse c) :
      CommonExec OrdExec q T S reverse c k (refused T S reverse c) []
  | returned (small : smaller T S reverse c)
      (execution : OrdExec (pair T S reverse c).1 (pair T S reverse c).2 q answer) :
      CommonExec OrdExec q T S reverse c k (returned T S reverse c answer)
        [⟨k,(pair T S reverse c,q),answer.map (fun fs=>(fs.length-1,fs)),true⟩]

variable {OrdExec : Tree→Tree→Nat→Option F→Prop}
  {base : Tree→Tree→Nat→Option F}
  {T S : Tree}

theorem common_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : CommonExec OrdExec q T S reverse c k out slots) :
    out=commonBranchMeter (fun b T S=>base T S b) (fun _ _ _=>0) q T S reverse c := by
  cases h with
  | refused large =>
    simp only [smaller,pair] at large
    simp only [commonBranchMeter,large,↓reduceIte,refused]
  | returned small execution =>
    have hv:=sound _ _ _ _ execution
    simp only [smaller,pair] at small
    simp only [pair] at hv
    simp only [commonBranchMeter,small,↓reduceIte,←hv]
    rfl

theorem common_exists (total : ∀ T S b,∃ a,OrdExec T S b a)
    (q : Nat) (T S : Tree) (reverse : Bool) (c : CherryBranching.Candidate) (k : Nat) :
    ∃ out slots,CommonExec OrdExec q T S reverse c k out slots := by
  by_cases small : smaller T S reverse c
  · obtain ⟨answer,execution⟩:=total (pair T S reverse c).1 (pair T S reverse c).2 q
    exact ⟨_,_,CommonExec.returned small execution⟩
  · exact ⟨_,_,CommonExec.refused small⟩

theorem common_slots_realize
    (h : CommonExec OrdExec q T S reverse c k out slots) :
    ∀ s∈slots,SlotRealizes OrdExec .direct s := by
  cases h with
  | refused large => simp
  | returned small execution =>
    intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact Or.inr ⟨rfl,rfl,_,execution,rfl⟩

def queries (q : Nat) (T S : Tree) (reverse : Bool) (c : CherryBranching.Candidate) : List Q :=
  if smaller T S reverse c then [(pair T S reverse c,q)] else []

theorem common_index (h : CommonExec OrdExec q T S reverse c k out slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k (queries q T S reverse c) := by
  cases h with
  | refused large => simp [queries,large,CallbackPairingAuthor.indexFrom]
  | returned small execution => simp [queries,small,CallbackPairingAuthor.indexFrom]

end SourceCommonV3
