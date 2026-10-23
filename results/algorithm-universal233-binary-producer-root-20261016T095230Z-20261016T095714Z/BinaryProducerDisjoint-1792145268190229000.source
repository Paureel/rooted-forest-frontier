import BinaryProducerPretest
namespace GenericForest.BinaryProducer
open BinaryProvider GenericForest.ScalarBits GenericForest.CheckCorrespondence Universal233.WholeSourceWork

def treePairValue (p : BinaryProvider.Tree×BinaryProvider.Tree) : RMAF.Tree×RMAF.Tree := (treeValue p.1,treeValue p.2)
theorem restrictLabels_value (B : Block) (T : BinaryProvider.Tree) :
 targetValue (restrictLabels B T).value=RMAF.restrict (blockValue B) (treeValue T) := by
 let C:=(prepareCapacity B [leavesBits T]).value
 have r:=prepareCapacity_spec B [leavesBits T]
 have p:=(restrictLabels_projects C.length B T r.1 (r.2.1 (leavesBits T) (by simp))).1
 exact p.trans (meterRestrict_value _ _)

def componentBits (t s : BinaryProvider.Tree) : Charged (Option (BinaryProvider.Tree×BinaryProvider.Tree)):=
 let l:=leavesCopy s;let r:=restrictLabels l.value t
 ⟨r.value.map (fun u=>(u,s)),l.work+r.work+4⟩
@[simp] theorem componentBits_value (t s : BinaryProvider.Tree) :
 (componentBits t s).value.map treePairValue=GenericForest.componentPair (treeValue t) (treeValue s) := by
 have h:=restrictLabels_value (leavesBits s) t
 simp only [leaves_projection] at h
 simp only [componentBits,leavesCopy_value,GenericForest.componentPair,←h]
 cases (restrictLabels (leavesBits s) t).value <;> rfl

def cutBits : Option RMAF.Vertex→Bits | none=>[] | some _=>[true]
@[simp] theorem cutBits_value (c : Option RMAF.Vertex) : decode (cutBits c)=Universal233.DepthOne.cutCost c := by
 cases c <;> rfl

def jobsBits (t : BinaryProvider.Tree) : List BinaryProvider.Tree→Charged (Option (List (Job (BinaryProvider.Tree×BinaryProvider.Tree) BinaryProvider.Forest)))
 | []=>⟨some [],1⟩
 | s::ss=>let c:=componentBits t s
  match c.value with
  | none=>⟨none,c.work+4⟩
  | some p=>let b:=pretestBits p.1 p.2
   match b.value with
   | .refused=>⟨none,c.work+b.work+4⟩
   | .rejected=>let r:=jobsBits t ss;⟨r.value.map (Job.hard p::·),c.work+b.work+r.work+8⟩
   | .found cut=>let f:=forestBits s cut;let r:=jobsBits t ss
                  ⟨r.value.map (Job.resolved p (cutBits cut) f.value::·),c.work+b.work+f.work+r.work+12⟩

@[simp] theorem jobsBits_value (t : BinaryProvider.Tree) (ss : List BinaryProvider.Tree) :
 (jobsBits t ss).value.map (List.map (jobValue treePairValue forestValue))=
 GenericForest.jobs (treeValue t) (sourcesValue ss) := by
 induction ss with
 | nil=>rfl
 | cons s ss ih=>
  have c:=componentBits_value t s
  cases hc : (componentBits t s).value with
  | none=>simp only [hc,Option.map_none] at c;simp [jobsBits,hc,sourcesValue,GenericForest.jobs,←c]
  | some p=>
   simp only [hc,Option.map_some] at c
   have b:=pretestBits_value p.1 p.2
   cases hb : (pretestBits p.1 p.2).value <;> simp only [hb] at b
   all_goals simp only [jobsBits,hc,hb,sourcesValue,List.map_cons,GenericForest.jobs,←c,Option.bind_some,treePairValue,←b]
   all_goals try simp only [Option.map_map,Function.comp_def,List.map_cons,jobValue,forestBits_value,cutBits_value]
   all_goals simp only [sourcesValue] at ih
   all_goals cases hr : (jobsBits t ss).value <;> simp only [Option.map_none,Option.map_some] at ih ⊢
   all_goals rw [←ih,hr];rfl

/-- The ordinary callback returns represented forests. Its length-to-cost
conversion is an executed bit counter followed by saturating subtraction. -/
def ordinaryAnswer (ordinary : BinaryProvider.Tree→BinaryProvider.Tree→Bits→Charged (Option BinaryProvider.Forest))
 (p : BinaryProvider.Tree×BinaryProvider.Tree) (b : Bits) : Charged (Option (Bits×BinaryProvider.Forest)):=
 let a:=ordinary p.1 p.2 b
 match a.value with
 | none=>⟨none,a.work+4⟩
 | some F=>let n:=spineCounter F;let c:=subtractBits n.value [true]
            ⟨some (c.value,F),a.work+n.work+c.work+8⟩

theorem ordinaryAnswer_value (ordinary : BinaryProvider.Tree→BinaryProvider.Tree→Bits→Charged (Option BinaryProvider.Forest))
 (native : RMAF.Tree→RMAF.Tree→Nat→Option GenericForest.Forest)
 (ih : ∀t s b,forestOptionValue (ordinary t s b).value=native (treeValue t) (treeValue s) (decode b))
 (p : BinaryProvider.Tree×BinaryProvider.Tree) (b : Bits) :
 (ordinaryAnswer ordinary p b).value.map (pairValue forestValue)=
 (native (treeValue p.1) (treeValue p.2) (decode b)).map (fun F=>(F.length-1,F)) := by
 have h:=ih p.1 p.2 b
 cases ha : (ordinary p.1 p.2 b).value with
 | none=>simp [ordinaryAnswer,ha,forestOptionValue] at h ⊢;rw [←h];rfl
 | some F=>
  simp only [forestOptionValue,ha,Option.map_some] at h
  simp [ordinaryAnswer,ha,←h,pairValue,subtractBits_value,spineCounter_value,forestValue_length,decode,bit]

def disjointProducer (ordinary : BinaryProvider.Tree→BinaryProvider.Tree→Bits→Charged (Option BinaryProvider.Forest))
 (t : BinaryProvider.Tree) (ss : List BinaryProvider.Tree) (q : Bits) : Charged (Option BinaryProvider.Forest):=
 let j:=jobsBits t ss
 match j.value with
 | none=>⟨none,j.work+4⟩
 | some js=>let r:=scheduleBits (ordinaryAnswer ordinary) q js
            let f:=BinaryCaller.disjointFinish t ss q r.value.answers
            ⟨f.value,j.work+r.work+f.work+8⟩

/-- This replaces the former arbitrary scheduler-answer representation premise
with concrete finite-bit jobs/pretest/scheduler and one typed ordinary IH. -/
theorem disjointProducer_value (ordinary : BinaryProvider.Tree→BinaryProvider.Tree→Bits→Charged (Option BinaryProvider.Forest))
 (native : RMAF.Tree→RMAF.Tree→Nat→Option GenericForest.Forest)
 (ih : ∀t s b,forestOptionValue (ordinary t s b).value=native (treeValue t) (treeValue s) (decode b))
 (t : BinaryProvider.Tree) (ss : List BinaryProvider.Tree) (q : Bits) :
 forestOptionValue (disjointProducer ordinary t ss q).value=
 GenericForest.disjointSolve (treeValue t) (sourcesValue ss) native (decode q) := by
 have j:=jobsBits_value t ss
 unfold GenericForest.disjointSolve GenericForest.disjointAttempt
 cases hj : (jobsBits t ss).value with
 | none=>simp only [hj,Option.map_none] at j;simp [disjointProducer,hj,←j,forestOptionValue]
 | some js=>
  simp only [hj,Option.map_some] at j
  have r:=scheduleBits_value treePairValue forestValue (ordinaryAnswer ordinary)
    (fun p b=>(native p.1 p.2 b).map (fun F=>(F.length-1,F)))
    (ordinaryAnswer_value ordinary native ih) q js
  have ra:=congrArg Universal233.PaidQueries.Receipt.answers r
  simp only [receiptValue] at ra
  have f:=BinaryCaller.disjoint_site t ss q (scheduleBits (ordinaryAnswer ordinary) q js).value.answers
  simp only [disjointProducer,hj,←j,Option.map_some,Option.bind_some]
  rw [f,←ra]
  cases hx : (scheduleBits (ordinaryAnswer ordinary) q js).value.answers with
  | none=>rfl
  | some xs=>
   simp only [Option.map_some,Option.bind_some]
   congr 1
   clear hx
   induction xs with
   | nil=>rfl
   | cons x xs ih=>simp only [forestValue] at ih;simp [List.flatMap_cons,pairValue,forestValue,List.map_append,ih]

/-- Direct singleton producer: no freely supplied candidate value remains. -/
def singletonProducer (ordinary : BinaryProvider.Tree→BinaryProvider.Tree→Bits→Charged (Option BinaryProvider.Forest))
 (t s : BinaryProvider.Tree) (q : Bits) : Charged (Option BinaryProvider.Forest):=
 let a:=ordinary t s q;let c:=BinaryCaller.checkOptional (some t) [s] q a.value
 ⟨c.value,a.work+c.work+4⟩
theorem singletonProducer_value (ordinary : BinaryProvider.Tree→BinaryProvider.Tree→Bits→Charged (Option BinaryProvider.Forest))
 (native : RMAF.Tree→RMAF.Tree→Nat→Option GenericForest.Forest)
 (ih : ∀t s b,forestOptionValue (ordinary t s b).value=native (treeValue t) (treeValue s) (decode b))
 (t s : BinaryProvider.Tree) (q : Bits) :
 forestOptionValue (singletonProducer ordinary t s q).value=
 (native (treeValue t) (treeValue s) (decode q)).bind
  (GenericForest.checked (some (treeValue t)) [treeValue s] (decode q)) := by
 exact (BinaryCaller.singleton_actual_call native t s q (ordinary t s q).value (ih t s q))
end GenericForest.BinaryProducer
