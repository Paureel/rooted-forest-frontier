import ClassifierPayload
open RMAF Universal233.Rule5PendantLocalWork
private def r : CheckRequest := .restriction (.leaf 0) (.leaf 0) [0]
private def no : Unit→CheckReceipt Bool := fun _=>⟨false,5,[r]⟩
private def yes : Unit→CheckReceipt Bool := fun _=>⟨true,7,[r,r]⟩
private def optionRow (n : Nat) : CheckReceipt (Option Nat) := ⟨if n=0 then some 9 else none,2,[r]⟩
example : (andSequence [no,yes]).value=false := by decide +kernel
example : (andSequence [no,yes]).work=6 := by decide +kernel
example : (andSequence [no,yes]).calls.length=1 := by decide +kernel
example : (andSequence [fun _=>⟨true,5,[r]⟩,yes]).work=18 := by decide +kernel
example : (optionsMeter optionRow [0,1,0]).value=[9,9] := by decide +kernel
example : (optionsMeter optionRow [0,1,0]).work=19 := by decide +kernel
example : (optionsHeadMeter ⟨[0,1,0],10⟩ optionRow).work=31 := by decide +kernel
example : (admittedMeter (fun _=>0) (.leaf 0) (.leaf 1) 0 1).value=false := by decide +kernel
example : (admittedMeter (fun _=>0) (.leaf 0) (.leaf 1) 0 1).work>1 := by decide +kernel
