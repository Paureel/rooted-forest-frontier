import DisjointRunBound
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork
open Universal233.BothBad Universal233.PaidQueries Universal233.BinaryCheap

def cheapColorMeter (A B D : List Nat) (x : Nat) : Charged Nat:=sideTaggedMeter B A D x
@[simp] theorem cheapColorMeter_value (A B D : List Nat) (x : Nat) :
 (cheapColorMeter A B D x).value=cheapColor A B D x:=by
 simpa only [cheapColorMeter,cheapColor] using sideTaggedMeter_value B A D x

def yesSideMeter (A D : List Nat) : Charged (List Nat):=meterFilter (fun x=>meterContains x D) A
def noSideMeter (A D : List Nat) : Charged (List Nat):=
 meterFilter (fun x=>let r:=meterContains x D;⟨!r.value,r.work+2⟩) A
@[simp] theorem yesSideMeter_value (A D : List Nat) : (yesSideMeter A D).value=ay A D:=by
 simp [yesSideMeter,ay,BinaryExchange.yes]
@[simp] theorem noSideMeter_value (A D : List Nat) : (noSideMeter A D).value=an A D:=by
 simp [noSideMeter,an,BinaryExchange.no]

def knownOneMeter (T S : Tree) (A : List Nat) : Charged (Option (List (List Nat))):=
 let t:=meterRestrict A T;let s:=meterRestrict A S
 match t.value,s.value with
 | some t',some s'=>let p:=meterPretest t' s'
   match p.value with
   | .found (some v)=>let f:=meterForest s' (some v);⟨some f.value,t.work+s.work+p.work+f.work+16⟩
   | _=>⟨none,t.work+s.work+p.work+12⟩
 | _,_=>⟨none,t.work+s.work+8⟩
@[simp] theorem knownOneMeter_value (T S : Tree) (A : List Nat) :
 (knownOneMeter T S A).value=knownOne T S A:=by
 simp only [knownOneMeter,knownOne,meterRestrict_value,meterPretest_value,meterForest_value]
 cases ht:restrict A T <;> cases hs:restrict A S <;> simp only []
 all_goals try rfl
 rename_i t s
 cases hp:DepthOne.pretest01 t s <;> try rfl
 rename_i c
 cases c <;> rfl

def entriesMeter (q : Nat) (mode : Mode) : List CoreProgram.Output→Charged (List Entry)
 | []=>⟨[],2⟩
 | o::os=>let r:=entriesMeter q mode os
   ⟨if o.sourceCuts.length+mode.extra≤q then
      ⟨o,mode,q-o.sourceCuts.length-mode.extra⟩::r.value else r.value,
     2*o.sourceCuts.length+r.work+20⟩
@[simp] theorem entriesMeter_value (q : Nat) (mode : Mode) (os : List CoreProgram.Output) :
 (entriesMeter q mode os).value=entries q mode os:=by
 induction os with
 | nil=>rfl
 | cons o os ih=>
   simp only [entriesMeter,entries,List.filterMap_cons,ih]
   split <;> rfl

def appendEntriesMeter (a b : Charged (List Entry)) : Charged (List Entry):=
 ⟨a.value++b.value,a.work+b.work+2*a.value.length+4⟩
@[simp] theorem appendEntriesMeter_value (a b : Charged (List Entry)) :
 (appendEntriesMeter a b).value=a.value++b.value:=rfl
end OrdinaryDispatch.Hard2SourceWork
