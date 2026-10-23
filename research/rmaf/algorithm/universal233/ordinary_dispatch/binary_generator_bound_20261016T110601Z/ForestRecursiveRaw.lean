import GeneratorStorageBinding
namespace GenericForest.BinaryProducer
open BinaryProvider GenericForest.ScalarBits Universal233.WholeSourceWork
theorem rawCandidates_value_below
 (solve : Option BinaryProvider.Tree→List BinaryProvider.Tree→Bits→Charged (Option BinaryProvider.Forest))
 (native : Option RMAF.Tree→List RMAF.Tree→Nat→Option GenericForest.Forest)
 (bound : Nat) (ih : ∀T ss b,decode b<bound→forestOptionValue (solve T ss b).value=native (targetValue T) (sourcesValue ss) (decode b))
 (T : Option BinaryProvider.Tree) (ss : List BinaryProvider.Tree) (q : Bits) (ios : List (Bits×Output)) (qb : decode q≤bound) :
 ((rawCandidates solve T ss q ios).value.map forestValue)=
 (ios.map branchValue).filterMap (fun io=>
  let d:=io.2.sourceCuts.length
  if 1≤d∧d≤decode q then native (targetValue T) (GenericForest.replace (sourcesValue ss) io.1 io.2.partition) (decode q-d) else none) := by
 induction ios with
 | nil=>rfl
 | cons io ios rec=>
  rcases io with ⟨i,o⟩
  simp only [rawCandidates,List.map_cons,List.filterMap_cons,branchValue,outputValue,
   leBits_value,spineCounter_value,decode,bit,Nat.mul_zero,Nat.add_zero,ite_true]
  by_cases guard : 1≤o.sourceCuts.length∧o.sourceCuts.length≤decode q
  · have g1 : (decide (1≤o.sourceCuts.length)&&decide (o.sourceCuts.length≤decode q))=true:=by simp [guard.1,guard.2]
    have decrease : decode (subtractBits q (spineCounter o.sourceCuts).value).value<bound:=by
     simp only [subtractBits_value,spineCounter_value];omega
    have a:=ih T (replaceBits o.partition i ss).value (subtractBits q (spineCounter o.sourceCuts).value).value decrease
    simp only [replaceBits_value,subtractBits_value,spineCounter_value] at a
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

theorem generatedRawParent_value_below
 (solve : Option BinaryProvider.Tree→List BinaryProvider.Tree→Bits→Charged (Option BinaryProvider.Forest))
 (native : Option RMAF.Tree→List RMAF.Tree→Nat→Option GenericForest.Forest)
 (bound : Nat) (ih : ∀T ss b,decode b<bound→forestOptionValue (solve T ss b).value=native (targetValue T) (sourcesValue ss) (decode b))
 (t : BinaryProvider.Tree) (ss : List BinaryProvider.Tree) (h : OverlapBits) (q : Bits) (qb : decode q≤bound) :
 forestOptionValue (generatedRawParent solve t ss h q).value=
 RMAF.best List.length (GenericForest.accepted (some (treeValue t)) (sourcesValue ss) (decode q))
 ((GenericForest.branches (treeValue t) (sourcesValue ss) (overlapValue h) (decode q)).filterMap (fun io=>
  let d:=io.2.sourceCuts.length
  if 1≤d∧d≤decode q then native (some (treeValue t)) (GenericForest.replace (sourcesValue ss) io.1 io.2.partition) (decode q-d) else none)) := by
 have a:=BinaryCaller.raw_parent_site (some t) ss q (rawCandidates solve (some t) ss q (branchesProducer t ss h q).value).value
 simp only [rawCandidates_value_below solve native bound ih _ _ q _ qb,branchesProducer_value,targetValue,Option.map_some,labelValue] at a
 exact a
end GenericForest.BinaryProducer
