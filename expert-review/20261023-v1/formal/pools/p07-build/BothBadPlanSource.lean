import BothBadPlannerAtoms
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork
open Universal233.BothBad Universal233.PaidQueries Universal233.BinaryCheap Universal233.RankConsumer

def cheapPlanMeter (S T : Tree) (A B C D : List Nat) (q : Nat)
 (cheap opposite : List CoreProgram.Output) : Charged (List Entry):=
 let y:=yesSideMeter A D;let n:=noSideMeter A D
 let gy:=meterRestrictionAgrees S T y.value;let gn:=meterRestrictionAgrees S T n.value
 let front:=y.work+n.work+gy.work+gn.work+12
 if gy.value&&gn.value then
  let known:=knownOneMeter T S A
  match known.value with
  | none=>⟨[],front+known.work+8⟩
  | some F=>let a:=entriesMeter q .ordinary cheap
            let b:=entriesMeter q (.retained A B C F) opposite
            let both:=appendEntriesMeter a b
            ⟨both.value,front+known.work+both.work+12⟩
 else
  let a:=entriesMeter q .ordinary cheap;let b:=entriesMeter q .full opposite
  let both:=appendEntriesMeter a b
  ⟨both.value,front+both.work+8⟩
@[simp] theorem cheapPlanMeter_value (S T : Tree) (A B C D : List Nat) (q : Nat)
 (cheap opposite : List CoreProgram.Output) :
 (cheapPlanMeter S T A B C D q cheap opposite).value=cheapPlan S T A B C D q cheap opposite:=by
 simp only [cheapPlanMeter,cheapPlan,yesSideMeter_value,noSideMeter_value,meterRestrictionAgrees_value,
  knownOneMeter_value,appendEntriesMeter_value,entriesMeter_value]
 split
 · cases h:knownOne T S A <;> rfl
 · rfl

def reuseOutputsMeter (S : Tree) (color : Nat→Charged Nat) (probe : List CoreProgram.Output) (q : Nat) : Charged (List CoreProgram.Output):=
 if probe.isEmpty then let r:=generatedOutputsMeter S color q;⟨r.value,r.work+4⟩ else ⟨probe,4⟩
@[simp] theorem reuseOutputsMeter_value (S : Tree) (color : Nat→Charged Nat)
 (probe : List CoreProgram.Output) (q : Nat) :
 (reuseOutputsMeter S color probe q).value=reuse S (fun x=>(color x).value) probe q:=by
 simp only [reuseOutputsMeter,reuse,generatedOutputsMeter_value]
 split <;> rfl

/-- Both fixed q3 probes are charged, and each branch pays exactly its literal
reuse/generate, entry filter and left-append construction. -/
def bothBadPlanMeter (S T : Tree) (A B C D : List Nat) (q : Nat) : Charged (List Entry):=
 if q<3 then ⟨[],4⟩ else
  let a:=generatedOutputsMeter S (cheapColorMeter A B D) 3
  let b:=generatedOutputsMeter S (cheapColorMeter B A D) 3
  if a.value.isEmpty then
   if b.value.isEmpty then
    let x:=generatedOutputsMeter S (cheapColorMeter A B D) q
    let y:=generatedOutputsMeter S (cheapColorMeter B A D) q
    let outputs:=appendOutputsMeter x y
    let entries:=entriesMeter q .full outputs.value
    ⟨entries.value,a.work+b.work+outputs.work+entries.work+16⟩
   else
    let opposite:=reuseOutputsMeter S (cheapColorMeter A B D) a.value q
    let cp:=cheapPlanMeter S T B A C D q b.value opposite.value
    ⟨cp.value,a.work+b.work+opposite.work+cp.work+16⟩
  else
   let opposite:=reuseOutputsMeter S (cheapColorMeter B A D) b.value q
   let cp:=cheapPlanMeter S T A B C D q a.value opposite.value
   ⟨cp.value,a.work+b.work+opposite.work+cp.work+16⟩
@[simp] theorem bothBadPlanMeter_value (S T : Tree) (A B C D : List Nat) (q : Nat) :
 (bothBadPlanMeter S T A B C D q).value=plan S T A B C D q:=by
 have ca:(fun x=>(cheapColorMeter A B D x).value)=cheapColor A B D:=funext (cheapColorMeter_value A B D)
 have cb:(fun x=>(cheapColorMeter B A D x).value)=cheapColor B A D:=funext (cheapColorMeter_value B A D)
 by_cases hq:q<3
 · simp only [bothBadPlanMeter,plan,hq,ite_true]
 · by_cases ha:(CoreProgram.generate S (cheapColor A B D) 3).outputs.isEmpty=true
   · by_cases hb:(CoreProgram.generate S (cheapColor B A D) 3).outputs.isEmpty=true
     all_goals simp only [bothBadPlanMeter,plan,generatedOutputsMeter_value,ca,cb,
       appendOutputsMeter_value,entriesMeter_value,cheapPlanMeter_value,reuseOutputsMeter_value,
       fourProbe,hq,ha,hb,ite_true,ite_false] <;> simp
   · simp only [bothBadPlanMeter,plan,generatedOutputsMeter_value,ca,cb,
       appendOutputsMeter_value,entriesMeter_value,cheapPlanMeter_value,reuseOutputsMeter_value,
       fourProbe,hq,ha,ite_true,ite_false] <;> simp
end OrdinaryDispatch.Hard2SourceWork
