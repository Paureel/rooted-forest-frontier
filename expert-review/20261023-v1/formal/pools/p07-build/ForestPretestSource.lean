import SourceBestMeter
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork

def unchangedForestMeter (ss : List Tree) : Charged (List (List Nat)):=meterMap meterLeaves ss
@[simp] theorem unchangedForestMeter_value (ss : List Tree) :
 (unchangedForestMeter ss).value=ForestPretest01.unchanged ss:=by simp [unchangedForestMeter,ForestPretest01.unchanged]

/-- Recompute the literal unchanged tail at every edge occurrence and the
literal leaves s at every lifted tail occurrence; both append copies are paid. -/
def oneCutsForestMeter : List Tree→Charged (List (List (List Nat)))
 | []=>⟨[],2⟩
 | s::ss=>
   let edges:=meterEdges s
   let head:=meterMap (fun p=>let f:=meterForest s (some p);let u:=unchangedForestMeter ss
      ⟨f.value++u.value,f.work+u.work+2*f.value.length+8⟩) edges.value
   let tail:=oneCutsForestMeter ss
   let lift:=meterMap (fun F=>let l:=meterLeaves s;⟨l.value::F,l.work+8⟩) tail.value
   ⟨head.value++lift.value,edges.work+head.work+tail.work+lift.work+2*head.value.length+12⟩
@[simp] theorem oneCutsForestMeter_value (ss : List Tree) :
 (oneCutsForestMeter ss).value=ForestPretest01.oneCuts ss:=by
 induction ss with
 | nil=>rfl
 | cons s ss ih=>simp only [oneCutsForestMeter,ForestPretest01.oneCuts,meterMap_value,meterEdges_value,
   meterForest_value,unchangedForestMeter_value,meterLeaves_value,ih]

def pretestCandidatesMeter (ss : List Tree) : Charged (List (List (List Nat))):=
 let u:=unchangedForestMeter ss;let c:=oneCutsForestMeter ss
 ⟨u.value::c.value,u.work+c.work+4⟩
@[simp] theorem pretestCandidatesMeter_value (ss : List Tree) :
 (pretestCandidatesMeter ss).value=ForestPretest01.candidates ss:=by
 simp [pretestCandidatesMeter,ForestPretest01.candidates]

def forestPretestMeter (T : Option Tree) (ss : List Tree) : Charged ForestPretest01.Result:=
 let p:=meterProper T ss
 if p.value then
  let c:=pretestCandidatesMeter ss
  let b:=sourceBestMeter (additionalCostMeter ss) (meterAgrees T ss) c.value
  ⟨match b.value with | none=>.rejected | some F=>.found F,p.work+c.work+b.work+16⟩
 else ⟨.refused,p.work+8⟩
@[simp] theorem forestPretestMeter_value (T : Option Tree) (ss : List Tree) :
 (forestPretestMeter T ss).value=ForestPretest01.pretest01 T ss:=by
 simp only [forestPretestMeter,ForestPretest01.pretest01,meterProper_value,
  pretestCandidatesMeter_value,sourceBestMeter_value,additionalCostMeter_value,meterAgrees_value]
 split
 · cases hb:best (additionalCost ss) (agrees T ss) (ForestPretest01.candidates ss) <;> rfl
 · rfl
end OrdinaryDispatch.Hard2SourceWork
