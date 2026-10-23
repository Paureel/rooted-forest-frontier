import ProducerCanonicalSites
namespace OrdinaryDispatch.StoredNumeric.ProducerBinding
open GenericForest.ScalarBits GenericForest.BinaryProvider Universal233.WholeSourceWork
open GenericForest.BinaryProducer

/-- Actual underlying solver work, with the same paid raw guards and every
ordered occurrence. This excludes exactly the new normalization overhead. -/
def rawCanonicalSolveWork
 (solve : Option GenericForest.BinaryProvider.Tree→List GenericForest.BinaryProvider.Tree→Bits→Charged (Option GenericForest.BinaryProvider.Forest))
 (T : Option GenericForest.BinaryProvider.Tree) (ss : List GenericForest.BinaryProvider.Tree) (q : Bits) : List (Bits×Output)→Nat
 | []=>0
 | (i,o)::ios=>
  let d:=spineCounter o.sourceCuts;let lo:=leBits [true] d.value;let hi:=leBits d.value q
  let rest:=rawCanonicalSolveWork solve T ss q ios
  if lo.value&&hi.value then
   let s:=replaceBits o.partition i ss;let b:=subtractBits q d.value
   (solve T s.value (trimBudget b.value).value).work+rest
  else rest

def rawCanonicalTrimWork (q : Bits) : List (Bits×Output)→Nat
 | []=>0
 | (_,o)::ios=>
  let d:=spineCounter o.sourceCuts;let lo:=leBits [true] d.value;let hi:=leBits d.value q
  let rest:=rawCanonicalTrimWork q ios
  if lo.value&&hi.value then 8*(subtractBits q d.value).value.length+5+rest else rest

theorem rawCanonicalCallback_ledger
 (solve : Option GenericForest.BinaryProvider.Tree→List GenericForest.BinaryProvider.Tree→Bits→Charged (Option GenericForest.BinaryProvider.Forest))
 (T : Option GenericForest.BinaryProvider.Tree) (ss : List GenericForest.BinaryProvider.Tree) (q : Bits) (ios : List (Bits×Output)) :
 rawCallbackWork (rawCallbackCanonical solve) T ss q ios=
 rawCanonicalSolveWork solve T ss q ios+rawCanonicalTrimWork q ios := by
 induction ios with
 | nil=>rfl
 | cons io ios ih=>
  rcases io with ⟨i,o⟩
  dsimp only [rawCallbackWork,rawCanonicalSolveWork,rawCanonicalTrimWork]
  split
  · simp only [rawCallbackCanonical,canonicalCall_work,ih];omega
  · exact ih

theorem rawCanonicalTrimWork_bound (q : Bits) (ios : List (Bits×Output)) (B D : Nat)
 (qw : q.length≤B) (cuts : ∀io∈ios,io.2.sourceCuts.length≤D) :
 rawCanonicalTrimWork q ios≤(8*(B+D+1)+5)*ios.length := by
 induction ios with
 | nil=>simp [rawCanonicalTrimWork]
 | cons io ios ih=>
  rcases io with ⟨i,o⟩
  have c:=cuts (i,o) (by simp)
  have r:=ih (fun io h=>cuts io (by simp [h]))
  have l:=spineCounter_length o.sourceCuts
  have b:=subtractBits_length q (spineCounter o.sourceCuts).value
  dsimp only [rawCanonicalTrimWork]
  split <;> simp only [List.length_cons,Nat.mul_add,Nat.mul_one] <;> omega

/-- All trims at reached raw callbacks are paid. Rejected and duplicate input
occurrences retain the frozen producer's guard/list accounting. -/
theorem rawCanonicalCandidates_paid
 (solve : Option GenericForest.BinaryProvider.Tree→List GenericForest.BinaryProvider.Tree→Bits→Charged (Option GenericForest.BinaryProvider.Forest))
 (T : Option GenericForest.BinaryProvider.Tree) (ss : List GenericForest.BinaryProvider.Tree) (q : Bits) (ios : List (Bits×Output))
 (N L I D B M : Nat) (ip : 1≤I) (qw : q.length≤B) (sc : SourcesWidth L ss)
 (sn : ∀s∈ss,Universal233.CoreWork.treeNodes (treeValue s)≤N) (caps : ∀io∈ios,BranchCaps N L I D M io) :
 (rawCandidates (rawCallbackCanonical solve) T ss q ios).work≤rawCanonicalSolveWork solve T ss q ios+
 rawCanonicalTrimWork q ios+rawLocalCost N L I D B ss.length M*(ios.length+1) := by
 rw [←rawCanonicalCallback_ledger]
 exact rawCandidates_ledger _ T ss q ios N L I D B M ip qw sc sn caps

def runCanonicalSolveWork {P A : Type} (solve : P→Bits→Charged (Option (Bits×A))) (b : Bits) : List (Job P A)→Nat
 | []=>0
 | .resolved _ _ _::js=>runCanonicalSolveWork solve b js
 | .hard p::js=>let a:=solve p (trimBudget b).value
                a.work+(match a.value with | none=>0 | some _=>runCanonicalSolveWork solve b js)

/-- Multiplicity is the actual reached hard callbacks, including the final
refusal. An early refusal does not charge later unexecuted callbacks. -/
theorem runCanonicalCallback_ledger {P A : Type} (solve : P→Bits→Charged (Option (Bits×A))) (b : Bits) (js : List (Job P A)) :
 runCallbackWork (fun p c=>canonicalCall (solve p) c) b js=runCanonicalSolveWork solve b js+
 (8*b.length+5)*(runBits (fun p c=>canonicalCall (solve p) c) b js).value.calls.length := by
 induction js with
 | nil=>simp [runCallbackWork,runCanonicalSolveWork,runBits]
 | cons j js ih=>
  cases j with
  | resolved p c a=>simpa only [runCallbackWork,runCanonicalSolveWork,runBits] using ih
  | hard p=>
   cases h : (solve p (trimBudget b).value).value <;>
    simp only [runCallbackWork,runCanonicalSolveWork,runBits,canonicalCall_value,canonicalCall_work,h,List.length_cons,List.length_singleton] <;>
    simp only [Nat.mul_add,Nat.mul_one] <;> omega

/-- A new wrapper at the complete concrete generated parent; generator and
checker costs remain their actual paid work. No generation polynomial is assumed. -/
theorem generatedRawParentCanonical_paid
 (solve : Option GenericForest.BinaryProvider.Tree→List GenericForest.BinaryProvider.Tree→Bits→Charged (Option GenericForest.BinaryProvider.Forest))
 (T : GenericForest.BinaryProvider.Tree) (ss : List GenericForest.BinaryProvider.Tree) (h : OverlapBits) (q : Bits) :
 (generatedRawParentCanonical solve T ss h q).work=
 (branchesProducer T ss h (trimBudget q).value).work+
 (rawParentProducer (rawCallbackCanonical solve) (some T) ss (trimBudget q).value
  (branchesProducer T ss h (trimBudget q).value).value).work+8*q.length+9 := by
 simp only [generatedRawParentCanonical,canonicalCall_work,generatedRawParent];omega
end OrdinaryDispatch.StoredNumeric.ProducerBinding
