import BinaryProducerSource
namespace GenericForest.BinaryProducer
open BinaryProvider GenericForest.ScalarBits Universal233.WholeSourceWork
structure Output where
 partition : BinaryProvider.Forest
 sourceCuts : List RMAF.Vertex
 deriving Repr
def outputValue (o : Output) : Universal233.CoreProgram.Output:=⟨forestValue o.partition,o.sourceCuts⟩
def branchValue (io : Bits×Output) : Nat×Universal233.CoreProgram.Output:=(decode io.1,outputValue io.2)

/-- Literal ordered filterMap stage. Empty and duplicate source partitions are
retained in the input; rejected occurrences still pay their actual guards. -/
def rawCandidates (solve : Option BinaryProvider.Tree→List BinaryProvider.Tree→Bits→Charged (Option BinaryProvider.Forest))
 (T : Option BinaryProvider.Tree) (ss : List BinaryProvider.Tree) (q : Bits) : List (Bits×Output)→Charged (List BinaryProvider.Forest)
 | []=>⟨[],1⟩
 | (i,o)::ios=>
  let d:=spineCounter o.sourceCuts;let lower:=leBits [true] d.value;let upper:=leBits d.value q
  let r:=rawCandidates solve T ss q ios
  if lower.value&&upper.value then
   let s:=replaceBits o.partition i ss;let b:=subtractBits q d.value;let a:=solve T s.value b.value
   ⟨match a.value with | none=>r.value | some F=>F::r.value,
    d.work+lower.work+upper.work+r.work+s.work+b.work+a.work+12⟩
  else ⟨r.value,d.work+lower.work+upper.work+r.work+8⟩

theorem rawCandidates_value
 (solve : Option BinaryProvider.Tree→List BinaryProvider.Tree→Bits→Charged (Option BinaryProvider.Forest))
 (native : Option RMAF.Tree→List RMAF.Tree→Nat→Option GenericForest.Forest)
 (ih : ∀T ss b,forestOptionValue (solve T ss b).value=native (targetValue T) (sourcesValue ss) (decode b))
 (T : Option BinaryProvider.Tree) (ss : List BinaryProvider.Tree) (q : Bits) (ios : List (Bits×Output)) :
 ((rawCandidates solve T ss q ios).value.map forestValue)=
 (ios.map branchValue).filterMap (fun io=>
  let d:=io.2.sourceCuts.length
  if 1≤d∧d≤decode q then native (targetValue T) (GenericForest.replace (sourcesValue ss) io.1 io.2.partition) (decode q-d) else none) := by
 induction ios with
 | nil=>rfl
 | cons io ios rec=>
  rcases io with ⟨i,o⟩
  have a:=ih T (replaceBits o.partition i ss).value (subtractBits q (spineCounter o.sourceCuts).value).value
  simp only [replaceBits_value,subtractBits_value,spineCounter_value] at a
  simp only [rawCandidates,List.map_cons,List.filterMap_cons,branchValue,outputValue,
   leBits_value,spineCounter_value,decode,bit,Nat.mul_zero,Nat.add_zero,ite_true]
  by_cases guard : 1≤o.sourceCuts.length∧o.sourceCuts.length≤decode q
  · have g1 : (decide (1≤o.sourceCuts.length)&&decide (o.sourceCuts.length≤decode q))=true:=by simp [guard.1,guard.2]
    simp only [g1,ite_true,if_pos guard]
    cases ha : (solve T (replaceBits o.partition i ss).value (subtractBits q (spineCounter o.sourceCuts).value).value).value with
    | none=>simp only [forestOptionValue,ha,Option.map_none] at a;simp only [←a,rec]
    | some F=>
     simp only [forestOptionValue,ha,Option.map_some] at a
     simp only [←a,List.map_cons,rec]
  · have g1 : (decide (1≤o.sourceCuts.length)&&decide (o.sourceCuts.length≤decode q))=false:=by
     by_cases a : 1≤o.sourceCuts.length
     · have b : ¬o.sourceCuts.length≤decode q:=fun b=>guard ⟨a,b⟩;simp [a,b]
     · simp [a]
    simp only [g1,Bool.false_eq_true,ite_false,if_neg guard,rec]

def rawParentProducer (solve : Option BinaryProvider.Tree→List BinaryProvider.Tree→Bits→Charged (Option BinaryProvider.Forest))
 (T : Option BinaryProvider.Tree) (ss : List BinaryProvider.Tree) (q : Bits) (ios : List (Bits×Output)) : Charged (Option BinaryProvider.Forest):=
 let c:=rawCandidates solve T ss q ios;let a:=BinaryCaller.bestCandidates T ss q c.value
 ⟨a.value,c.work+a.work+4⟩

theorem rawParentProducer_value
 (solve : Option BinaryProvider.Tree→List BinaryProvider.Tree→Bits→Charged (Option BinaryProvider.Forest))
 (native : Option RMAF.Tree→List RMAF.Tree→Nat→Option GenericForest.Forest)
 (ih : ∀T ss b,forestOptionValue (solve T ss b).value=native (targetValue T) (sourcesValue ss) (decode b))
 (T : Option BinaryProvider.Tree) (ss : List BinaryProvider.Tree) (q : Bits) (ios : List (Bits×Output)) :
 forestOptionValue (rawParentProducer solve T ss q ios).value=
 RMAF.best List.length (GenericForest.accepted (targetValue T) (sourcesValue ss) (decode q))
  ((ios.map branchValue).filterMap (fun io=>
    let d:=io.2.sourceCuts.length
    if 1≤d∧d≤decode q then native (targetValue T) (GenericForest.replace (sourcesValue ss) io.1 io.2.partition) (decode q-d) else none)) := by
 have a:=BinaryCaller.raw_parent_site T ss q (rawCandidates solve T ss q ios).value
 simpa only [rawParentProducer,rawCandidates_value solve native ih,labelValue] using a

theorem rawCandidates_count
 (solve : Option BinaryProvider.Tree→List BinaryProvider.Tree→Bits→Charged (Option BinaryProvider.Forest))
 (T : Option BinaryProvider.Tree) (ss : List BinaryProvider.Tree) (q : Bits) (ios : List (Bits×Output)) :
 (rawCandidates solve T ss q ios).value.length≤ios.length := by
 induction ios with
 | nil=>simp [rawCandidates]
 | cons io ios ih=>
  rcases io with ⟨i,o⟩
  simp only [rawCandidates,List.length_cons]
  split
  · split <;> simp only [List.length_cons] <;> omega
  · dsimp only [Charged.value];omega

theorem rawParentProducer_paid
 (solve : Option BinaryProvider.Tree→List BinaryProvider.Tree→Bits→Charged (Option BinaryProvider.Forest))
 (T : Option BinaryProvider.Tree) (ss : List BinaryProvider.Tree) (q : Bits) (ios : List (Bits×Output)) :
 (rawParentProducer solve T ss q ios).work=
 (rawCandidates solve T ss q ios).work+(BinaryCaller.bestCandidates T ss q (rawCandidates solve T ss q ios).value).work+4 := rfl
end GenericForest.BinaryProducer
