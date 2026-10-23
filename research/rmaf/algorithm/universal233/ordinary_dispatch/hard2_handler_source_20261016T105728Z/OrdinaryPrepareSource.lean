import GoodPairSelectedBound
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork
open Universal233.PaidQueries Universal233.MafScheduler

def properBlockMeter (T S : Tree) (U : List Nat) : Charged Bool:=
 let n:=meterNodup U
 let all:=meterAll (fun x=>let t:=meterLeaves T;let s:=meterLeaves S
  let a:=meterContains x t.value;let b:=meterContains x s.value
  ⟨a.value&&b.value,t.work+s.work+a.work+b.work+4⟩) U
 ⟨n.value && !U.isEmpty && all.value,n.work+all.work+8⟩
@[simp] theorem properBlockMeter_value (T S : Tree) (U : List Nat) :
 (properBlockMeter T S U).value=properBlock T S U:=by simp [properBlockMeter,properBlock]

def ordinarySlotMeter (T S : Tree) (U : List Nat) : Charged (Option (Job (List Nat) (List (List Nat)))):=
 let p:=properBlockMeter T S U
 if !p.value then ⟨none,p.work+6⟩ else
  let t:=meterRestrict U T;let s:=meterRestrict U S
  match t.value,s.value with
  | some t',some s'=>
   let pre:=meterPretest t' s'
   match pre.value with
   | .refused=>⟨none,p.work+t.work+s.work+pre.work+12⟩
   | .rejected=>⟨some (.hard U),p.work+t.work+s.work+pre.work+12⟩
   | .found c=>let f:=meterForest s' c
               ⟨some (.resolved U (DepthOne.cutCost c) f.value),p.work+t.work+s.work+pre.work+f.work+16⟩
  | _,_=>⟨none,p.work+t.work+s.work+10⟩
@[simp] theorem ordinarySlotMeter_value (T S : Tree) (U : List Nat) :
 (ordinarySlotMeter T S U).value=slot T S U:=by
 simp only [ordinarySlotMeter,slot,properBlockMeter_value,meterRestrict_value,meterPretest_value,meterForest_value]
 split
 · rfl
 · cases ht:restrict U T <;> cases hs:restrict U S <;> simp only []
   all_goals try rfl
   rename_i t s
   cases pre:DepthOne.pretest01 t s <;> rfl

/-- Conservative full traversal: the tail is charged even if an earlier slot
refuses. The value keeps the original short-circuit Option result. -/
def ordinaryPrepareMeter (T S : Tree) : List (List Nat)→Charged (Option (List (Job (List Nat) (List (List Nat)))))
 | []=>⟨some [],2⟩
 | U::Q=>let s:=ordinarySlotMeter T S U;let r:=ordinaryPrepareMeter T S Q
           ⟨s.value.bind (fun j=>r.value.map (j::·)),s.work+r.work+8⟩
@[simp] theorem ordinaryPrepareMeter_value (T S : Tree) (Q : List (List Nat)) :
 (ordinaryPrepareMeter T S Q).value=prepare T S Q:=by
 induction Q <;> simp_all [ordinaryPrepareMeter,prepare]
end OrdinaryDispatch.Hard2SourceWork
