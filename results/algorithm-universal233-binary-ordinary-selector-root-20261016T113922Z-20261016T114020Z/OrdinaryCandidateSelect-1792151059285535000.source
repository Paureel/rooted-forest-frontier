import OrdinaryCherries
namespace GenericForest.BinaryProducer.OrdinaryBits
open BinaryProvider GenericForest.ScalarBits Universal233.WholeSourceWork
abbrev Priority:=Universal233.CherryBranching.Priority
structure Candidate where
 parent : RMAF.Vertex
 a : Bits
 b : Bits
 originalCuts : Addresses
 deriving Repr

def candidateValue (c : Candidate) : Universal233.CherryBranching.Candidate :=
 ⟨c.parent,decode c.a,decode c.b,c.originalCuts⟩

def buildCandidates (S : BinaryProvider.Tree) : List Cherry→Charged (List Candidate)
 | []=>⟨[],1⟩
 | (p,a,b)::cs=>let cuts:=cutsBits S a b;let r:=buildCandidates S cs
                ⟨⟨p,a,b,cuts.value⟩::r.value,cuts.work+r.work+16⟩

def candidatesBits (T S : BinaryProvider.Tree) : Charged (List Candidate):=
 let cs:=cherriesBits T;let r:=buildCandidates S cs.value;⟨r.value,cs.work+r.work+4⟩

theorem buildCandidates_value (S : BinaryProvider.Tree) (cs : List Cherry) :
 (buildCandidates S cs).value.map candidateValue=(cs.map cherryValue).map (fun (p,a,b)=>
  (⟨p,a,b,Universal233.CherryBranching.cuts (treeValue S) a b⟩:Universal233.CherryBranching.Candidate)) := by
 induction cs with
 | nil=>rfl
 | cons c cs ih=>rcases c with ⟨p,a,b⟩;simp only [buildCandidates,List.map_cons,candidateValue,cherryValue,cutsBits_value,ih]

theorem candidatesBits_value (T S : BinaryProvider.Tree) :
 (candidatesBits T S).value.map candidateValue=Universal233.CherryBranching.candidates (treeValue T) (treeValue S) := by
 simp only [candidatesBits,buildCandidates_value,cherriesBits_value,Universal233.CherryBranching.candidates]

def isCommon (c : Candidate) : Charged Bool:=⟨c.originalCuts.isEmpty,4⟩
def isOne (c : Candidate) : Charged Bool:=let n:=spineCounter c.originalCuts;let e:=copiedEqual n.value [true];⟨e.value,n.work+e.work+4⟩
def isHigh (c : Candidate) : Charged Bool:=let n:=spineCounter c.originalCuts;let e:=leBits [true,true] n.value;⟨e.value,n.work+e.work+4⟩
@[simp] theorem isOne_value (c : Candidate) : (isOne c).value=(c.originalCuts.length==1) := by simp [isOne,decode,bit]
@[simp] theorem isHigh_value (c : Candidate) : (isHigh c).value=decide (3≤c.originalCuts.length) := by simp [isHigh,decode,bit]

def findCandidate (test : Candidate→Charged Bool) : List Candidate→Charged (Option Candidate)
 | []=>⟨none,1⟩
 | c::cs=>let p:=test c
           if p.value then ⟨some c,p.work+4⟩ else let r:=findCandidate test cs;⟨r.value,p.work+r.work+4⟩

theorem findCandidate_value (test : Candidate→Charged Bool) (native : Universal233.CherryBranching.Candidate→Bool)
 (ih : ∀c,(test c).value=native (candidateValue c)) (cs : List Candidate) :
 (findCandidate test cs).value.map candidateValue=(cs.map candidateValue).find? native := by
 induction cs with
 | nil=>rfl
 | cons c cs prev=>simp only [findCandidate,ih,List.map_cons,List.find?_cons];split <;> simp_all only [Option.map_some]

def selectedValue (p : Priority×Candidate) : Priority×Universal233.CherryBranching.Candidate :=(p.1,candidateValue p.2)

def selectCandidates (cs : List Candidate) : Charged (Option (Priority×Candidate)):=
 let common:=findCandidate isCommon cs
 match common.value with
 | some c=>⟨some (.common,c),common.work+4⟩
 | none=>let one:=findCandidate isOne cs
  match one.value with
  | some c=>⟨some (.one,c),common.work+one.work+8⟩
  | none=>let high:=findCandidate isHigh cs
   match high.value with
   | some c=>⟨some (.high,c),common.work+one.work+high.work+12⟩
   | none=>⟨cs.head?.map (.hard2,·),common.work+one.work+high.work+16⟩

def selectBits (T S : BinaryProvider.Tree) : Charged (Option (Priority×Candidate)):=
 let cs:=candidatesBits T S;let r:=selectCandidates cs.value;⟨r.value,cs.work+r.work+4⟩

theorem selectCandidates_value (cs : List Candidate) :
 (selectCandidates cs).value.map selectedValue=
 (match (cs.map candidateValue).find? (fun c=>c.originalCuts.isEmpty) with
 | some c=>some (.common,c)
 | none=>match (cs.map candidateValue).find? (fun c=>c.originalCuts.length==1) with
   | some c=>some (.one,c)
   | none=>match (cs.map candidateValue).find? (fun c=>decide (3≤c.originalCuts.length)) with
     | some c=>some (.high,c)
     | none=>(cs.map candidateValue).head?.map (.hard2,·)) := by
 have c:=findCandidate_value isCommon (fun c=>c.originalCuts.isEmpty) (by intros;rfl) cs
 have o:=findCandidate_value isOne (fun c=>c.originalCuts.length==1) (by intro c;exact isOne_value c) cs
 have h:=findCandidate_value isHigh (fun c=>decide (3≤c.originalCuts.length)) (by intro c;exact isHigh_value c) cs
 simp only [selectCandidates,←c,←o,←h]
 cases hc : (findCandidate isCommon cs).value with
 | some c=>rfl
 | none=>
  cases ho : (findCandidate isOne cs).value with
  | some c=>rfl
  | none=>
   cases hh : (findCandidate isHigh cs).value with
   | some c=>rfl
   | none=>cases cs <;> rfl

theorem selectBits_value (T S : BinaryProvider.Tree) :
 (selectBits T S).value.map selectedValue=Universal233.CherryBranching.select (treeValue T) (treeValue S) := by
 simp only [selectBits,selectCandidates_value,candidatesBits_value,Universal233.CherryBranching.select]
 rfl
end GenericForest.BinaryProducer.OrdinaryBits
