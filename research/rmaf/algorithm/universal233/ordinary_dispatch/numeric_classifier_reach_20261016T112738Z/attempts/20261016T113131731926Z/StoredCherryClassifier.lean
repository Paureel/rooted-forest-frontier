import ProducerBindingInterface
namespace OrdinaryDispatch.StoredNumeric.ClassifierReach
open GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.BinaryProducer
open OrdinaryDispatch.StoredNumeric.ProducerBinding Universal233.WholeSourceWork Universal233.CoreWork

structure CherryBits where
 parent : RMAF.Vertex
 a : Bits
 b : Bits
 deriving Repr

def cherryValue (c : CherryBits) : RMAF.Vertex×Nat×Nat :=(c.parent,decode c.a,decode c.b)

def prependCherries (side : Bool) : List CherryBits→Charged (List CherryBits)
 | []=>⟨[],1⟩
 | c::cs=>let r:=prependCherries side cs;⟨{c with parent:=side::c.parent}::r.value,r.work+8⟩
@[simp] theorem prependCherries_value (side : Bool) (cs : List CherryBits) :
 (prependCherries side cs).value.map cherryValue=(cs.map cherryValue).map (fun (p,a,b)=>(side::p,a,b)) := by
 induction cs <;> simp_all [prependCherries,cherryValue]
@[simp] theorem prependCherries_work (side : Bool) (cs : List CherryBits) :
 (prependCherries side cs).work=8*cs.length+1 := by induction cs <;> simp only [prependCherries,List.length_nil,List.length_cons] at * <;> omega

def cherriesBits : GenericForest.BinaryProvider.Tree→Charged (List CherryBits)
 | .leaf _=>⟨[],4⟩
 | .node (.leaf a) (.leaf b)=>let x:=copyBits a;let y:=copyBits b;⟨[⟨[],x.value,y.value⟩],x.work+y.work+12⟩
 | .node l r=>let a:=cherriesBits l;let b:=cherriesBits r
               let x:=prependCherries false a.value;let y:=prependCherries true b.value
               let z:=appendSpine x.value y.value
               ⟨z.value,a.work+b.work+x.work+y.work+z.work+12⟩

@[simp] theorem cherriesBits_value (T : GenericForest.BinaryProvider.Tree) :
 (cherriesBits T).value.map cherryValue=Universal233.CherryBranching.cherries (treeValue T) := by
 induction T with
 | leaf x=>rfl
 | node l r il ir=>
  cases l <;> cases r <;> simp_all [cherriesBits,Universal233.CherryBranching.cherries,treeValue,cherryValue,labelValue,List.map_map,Function.comp_def]

theorem prependCherries_provenance (side : Bool) (cs : List CherryBits) (c : CherryBits)
 (h : c∈(prependCherries side cs).value) :
 ∃d,d∈cs ∧ c={d with parent:=side::d.parent} := by
 induction cs with
 | nil=>simp [prependCherries] at h
 | cons d ds ih=>
  simp only [prependCherries,List.mem_cons] at h
  rcases h with rfl|hh
  · exact ⟨d,by simp,rfl⟩
  · obtain ⟨e,he,eq⟩:=ih hh;exact ⟨e,by simp [he],eq⟩

theorem cherriesBits_provenance (T : GenericForest.BinaryProvider.Tree) (c : CherryBits) (h : c∈(cherriesBits T).value) :
 c.a∈leavesBits T ∧ c.b∈leavesBits T ∧ c.parent.length≤treeNodes (treeValue T) := by
 induction T generalizing c with
 | leaf x=>simp [cherriesBits] at h
 | node l r il ir=>
  cases l with
  | leaf x=>
   cases r with
   | leaf y=>
    simp only [cherriesBits,copyBits_value,List.mem_singleton] at h;subst c
    simp [leavesBits,treeValue,treeNodes]
   | node u v=>
    simp only [cherriesBits,appendSpine_value,List.mem_append] at h
    rcases h with hh|hh
    · obtain ⟨d,hd,eq⟩:=prependCherries_provenance false _ c hh;simp [cherriesBits] at hd
    · obtain ⟨d,hd,eq⟩:=prependCherries_provenance true _ c hh
      obtain ⟨ha,hb,hp⟩:=ir d hd;subst c
      exact ⟨List.mem_append_right _ ha,List.mem_append_right _ hb,by simp only [treeValue,treeNodes,List.length_cons];omega⟩
  | node u v=>
   simp only [cherriesBits,appendSpine_value,List.mem_append] at h
   rcases h with hh|hh
   · obtain ⟨d,hd,eq⟩:=prependCherries_provenance false _ c hh
     obtain ⟨ha,hb,hp⟩:=il d hd;subst c
     exact ⟨List.mem_append_left _ ha,List.mem_append_left _ hb,by simp only [treeValue,treeNodes,List.length_cons];omega⟩
   · obtain ⟨d,hd,eq⟩:=prependCherries_provenance true _ c hh
     obtain ⟨ha,hb,hp⟩:=ir d hd;subst c
     exact ⟨List.mem_append_right _ ha,List.mem_append_right _ hb,by simp only [treeValue,treeNodes,List.length_cons];omega⟩

structure CandidateBits where
 parent : RMAF.Vertex
 a : Bits
 b : Bits
 originalCuts : Addresses
 deriving Repr

def candidateValue (c : CandidateBits) : Universal233.CherryBranching.Candidate:=⟨c.parent,decode c.a,decode c.b,c.originalCuts⟩

def candidatesFrom (S : GenericForest.BinaryProvider.Tree) : List CherryBits→Charged (List CandidateBits)
 | []=>⟨[],1⟩
 | c::cs=>let p:=pendantBits S c.a c.b;let r:=candidatesFrom S cs
           ⟨⟨c.parent,c.a,c.b,p.value⟩::r.value,p.work+r.work+8⟩
@[simp] theorem candidatesFrom_value (S : GenericForest.BinaryProvider.Tree) (cs : List CherryBits) :
 (candidatesFrom S cs).value.map candidateValue=(cs.map cherryValue).map
 (fun (p,a,b)=>⟨p,a,b,Universal233.CherryBranching.cuts (treeValue S) a b⟩) := by
 induction cs <;> simp_all [candidatesFrom,candidateValue,cherryValue]

def candidatesBits (T S : GenericForest.BinaryProvider.Tree) : Charged (List CandidateBits):=
 let c:=cherriesBits T;let s:=candidatesFrom S c.value;⟨s.value,c.work+s.work+4⟩
@[simp] theorem candidatesBits_value (T S : GenericForest.BinaryProvider.Tree) :
 (candidatesBits T S).value.map candidateValue=Universal233.CherryBranching.candidates (treeValue T) (treeValue S) := by
 simp only [candidatesBits,candidatesFrom_value,cherriesBits_value,Universal233.CherryBranching.candidates]

def cutClass (p : Universal233.CherryBranching.Priority) (cs : Addresses) : Bool :=
 match p,cs with
 | .common,[]=>true | .one,[_]=>true | .high,_::_::_::_=>true | _,_=>false
@[simp] theorem cutClass_common (cs : Addresses) : cutClass .common cs=cs.isEmpty := by cases cs <;> rfl
@[simp] theorem cutClass_one (cs : Addresses) : cutClass .one cs=(cs.length==1) := by cases cs with | nil=>rfl | cons x xs=>cases xs <;> simp [cutClass]
@[simp] theorem cutClass_high (cs : Addresses) : cutClass .high cs=decide (3≤cs.length) := by
 cases cs with | nil=>rfl | cons a as=>cases as with | nil=>rfl | cons b bs=>cases bs with | nil=>rfl | cons c cs=>simp [cutClass]

def findClass (p : Universal233.CherryBranching.Priority) : List CandidateBits→Charged (Option CandidateBits)
 | []=>⟨none,4⟩
 | c::cs=>if cutClass p c.originalCuts then ⟨some c,16⟩ else let r:=findClass p cs;⟨r.value,r.work+16⟩
@[simp] theorem findClass_value (p : Universal233.CherryBranching.Priority) (cs : List CandidateBits) :
 (findClass p cs).value.map candidateValue=(cs.map candidateValue).find? (fun c=>cutClass p c.originalCuts) := by
 induction cs with
 | nil=>rfl
 | cons c cs ih=>
  simp only [findClass,List.map_cons,List.find?_cons,candidateValue]
  split
  · rfl
  · exact ih

def selectCandidatesBits (cs : List CandidateBits) : Charged (Option (Universal233.CherryBranching.Priority×CandidateBits)):=
 let a:=findClass .common cs
 match a.value with
 | some c=>⟨some (.common,c),a.work+4⟩
 | none=>let b:=findClass .one cs
         match b.value with
         | some c=>⟨some (.one,c),a.work+b.work+8⟩
         | none=>let h:=findClass .high cs
                 match h.value with
                 | some c=>⟨some (.high,c),a.work+b.work+h.work+12⟩
                 | none=>⟨cs.head?.map (fun c=>(.hard2,c)),a.work+b.work+h.work+16⟩

def selectedValue (x : Universal233.CherryBranching.Priority×CandidateBits) :=(x.1,candidateValue x.2)
def selectPriorityBits (T S : GenericForest.BinaryProvider.Tree) : Charged (Option (Universal233.CherryBranching.Priority×CandidateBits)) :=
 let cs:=candidatesBits T S;let r:=selectCandidatesBits cs.value;⟨r.value,cs.work+r.work+4⟩

@[simp] theorem selectCandidatesBits_value (cs : List CandidateBits) :
 (selectCandidatesBits cs).value.map selectedValue=
 let ns:=cs.map candidateValue
 match ns.find? (fun c=>c.originalCuts.isEmpty) with
 | some c=>some (.common,c)
 | none=>match ns.find? (fun c=>c.originalCuts.length==1) with
   | some c=>some (.one,c)
   | none=>match ns.find? (fun c=>3≤c.originalCuts.length) with
     | some c=>some (.high,c)
     | none=>ns.head?.map (fun c=>(.hard2,c)) := by
 dsimp only [selectCandidatesBits]
 have a:=findClass_value .common cs;have b:=findClass_value .one cs;have h:=findClass_value .high cs
 simp only [cutClass_common,cutClass_one,cutClass_high] at a b h
 rw [←a,←b,←h]
 cases ha : (findClass .common cs).value <;> cases hb : (findClass .one cs).value <;> cases hh : (findClass .high cs).value <;>
  simp [selectedValue,Option.map_map,List.head?_map,Function.comp_def]

@[simp] theorem selectPriorityBits_value (T S : GenericForest.BinaryProvider.Tree) :
 (selectPriorityBits T S).value.map selectedValue=Universal233.CherryBranching.select (treeValue T) (treeValue S) := by
 simp only [selectPriorityBits,selectCandidatesBits_value,candidatesBits_value,Universal233.CherryBranching.select]
end OrdinaryDispatch.StoredNumeric.ClassifierReach
