import Lean
import Controls
open Lean RMAF Universal233.CoreProgram Universal233.CoreWork

def jAddr (v : Vertex) : String := String.ofList (v.map (fun b => if b then '1' else '0'))
def jGroup (g : Group) : Json := Json.arr #[toJson (jAddr g.origin),toJson g.labels,toJson g.color]
def jView (t : Option GTree) : Json := match t with
  | none => Json.mkObj [("root",Json.null),("groups",toJson ([] : List Json))]
  | some t => Json.mkObj [("root",toJson (jAddr (match t with | .leaf g => g.origin | .node p _ _ => p))), ("groups",toJson ((groups t).map jGroup))]
def jReceipt (r : Receipt) : Json := Json.mkObj [
  ("outputs",toJson (r.outputs.map (fun o => Json.mkObj [("partition",toJson o.partition),("cuts",toJson (o.sourceCuts.map jAddr))]))),
  ("refusals",toJson r.refusals),("visited",toJson r.visited),("childAttempts",toJson r.childAttempts),("pruned",toJson r.pruned)]
def jChoice (c : Choice) : Json := match c with
  | .finish => Json.mkObj [("kind",toJson "finish"),("origins",toJson ([] : List String))]
  | .one a => Json.mkObj [("kind",toJson "one"),("origins",toJson [jAddr a.origin])]
  | .two a b => Json.mkObj [("kind",toJson "two"),("origins",toJson [jAddr a.origin,jAddr b.origin])]
  | .refuse why => Json.mkObj [("kind",toJson "refuse"),("refusals",toJson [why])]
def emitReview (id : String) (value metrics : Json) : IO Unit := IO.println ("LEDGER_COMPARE "++(Json.mkObj [("id",toJson id),("value",value),("metrics",metrics)]).compress)


#eval do
  emitReview "empty-left-append-call-still-present" (toJson (([] : List Nat) ++ [1,2])) (Json.mkObj [])

#eval do
  emitReview "nonempty-left-append-work" (toJson (([10,11,12] : List Nat) ++ [20])) (Json.mkObj [])

#eval do
  let a := (⟨List.replicate 3 ⟨[],[]⟩,["a","b"],2,4,6⟩ : Receipt)
  let b := (⟨List.replicate 2 ⟨[],[]⟩,["c"],3,5,7⟩ : Receipt)
  let r := combine a b
  emitReview "combine-materializes-both-left-lists" (Json.mkObj [("outputs_length",toJson r.outputs.length),("refusals_length",toJson r.refusals.length),("visited",toJson r.visited),("childAttempts",toJson r.childAttempts),("pruned",toJson r.pruned)]) (Json.mkObj [("copied",toJson (appendCells a))])

#eval do
  let a := (⟨List.replicate 0 ⟨[],[]⟩,[],0,0,0⟩ : Receipt)
  let b := (⟨List.replicate 1 ⟨[],[]⟩,["r"],0,0,0⟩ : Receipt)
  let r := combine a b
  emitReview "combine-empty-left-lists" (Json.mkObj [("outputs_length",toJson r.outputs.length),("refusals_length",toJson r.refusals.length),("visited",toJson r.visited),("childAttempts",toJson r.childAttempts),("pruned",toJson r.pruned)]) (Json.mkObj [("copied",toJson (appendCells a))])

#eval do
  let a := (⟨List.replicate 8 ⟨[],[]⟩,[],0,0,0⟩ : Receipt)
  let b := (⟨List.replicate 1 ⟨[],[]⟩,[],0,0,0⟩ : Receipt)
  let r := combine a b
  emitReview "combine-left-output-length-eight" (Json.mkObj [("outputs_length",toJson r.outputs.length),("refusals_length",toJson r.refusals.length),("visited",toJson r.visited),("childAttempts",toJson r.childAttempts),("pruned",toJson r.pruned)]) (Json.mkObj [("copied",toJson (appendCells a))])

#eval do
  let a := (⟨List.replicate 16 ⟨[],[]⟩,[],0,0,0⟩ : Receipt)
  let b := (⟨List.replicate 1 ⟨[],[]⟩,[],0,0,0⟩ : Receipt)
  let r := combine a b
  emitReview "combine-left-output-length-sixteen" (Json.mkObj [("outputs_length",toJson r.outputs.length),("refusals_length",toJson r.refusals.length),("visited",toJson r.visited),("childAttempts",toJson r.childAttempts),("pruned",toJson r.pruned)]) (Json.mkObj [("copied",toJson (appendCells a))])

#eval do
  let r := meterFromTree (fun x : Nat => x) [] (.leaf 7)
  emitReview "singleton-fromTree-color-oracle" (jView (some r.tree)) (Json.mkObj [("oracleCalls",toJson (r.oracleCalls)),("footprint",toJson (footprint r.tree))])

#eval do
  let r := meterFromTree (fun x : Nat => x) [] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
  emitReview "fromTree-three-leaves-original-address-work" (jView (some r.tree)) (Json.mkObj [("oracleCalls",toJson (r.oracleCalls)),("footprint",toJson (footprint r.tree))])

#eval do
  let r := meterFromTree (fun x : Nat => x) [true,false] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
  emitReview "fromTree-nonempty-original-prefix" (jView (some r.tree)) (Json.mkObj [("oracleCalls",toJson (r.oracleCalls)),("footprint",toJson (footprint r.tree))])

#eval do
  let t := (fromTree (fun _ : Nat => 7) [] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)))
  emitReview "normalization-homogeneous-payload-appends" (jView (some (normalize t))) (Json.mkObj [("normalizeWork",toJson (normalizeWork t))])

#eval do
  let t := (fromTree (fun x : Nat => if x = 0 then 0 else if x = 1 then 0 else if x = 2 then 1 else 0) [] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)))
  emitReview "normalization-mixed-comparison-still-charged" (jView (some (normalize t))) (Json.mkObj [("normalizeWork",toJson (normalizeWork t))])

#eval do
  let t := (fromTree (fun x : Nat => x) [] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)))
  emitReview "groups-left-appends" (toJson ((groups t).map jGroup)) (Json.mkObj [("groupsWork",toJson (groupsWork t))])

#eval do
  let t := (fromTree (fun x : Nat => x) [] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)))
  emitReview "erase-suppressed-survivor-still-visits" (jView (erase [false,false] t)) (Json.mkObj [("eraseWork",toJson (eraseWork [false,false] t))])

#eval do
  let t := (fromTree (fun x : Nat => x) [] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)))
  emitReview "erase-original-root-cost" (jView (erase [] t)) (Json.mkObj [("eraseWork",toJson (eraseWork [] t))])

#eval do
  let t := (normalize (fromTree (fun x : Nat => if x = 0 then 0 else if x = 1 then 0 else if x = 2 then 1 else 0) [] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))))
  emitReview "choose-filter-find-list-work" (jChoice (choose t)) (Json.mkObj [("findFilterWork",toJson (findFilterWork (groups t) (groups t)))])

#eval do
  let t := (fromTree (fun x : Nat => if x = 0 then 0 else if x = 1 then 0 else if x = 2 then 1 else if x = 3 then 1 else 0) [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))))
  emitReview "choose-refusal-after-real-search" (jChoice (choose t)) (Json.mkObj [("findFilterWork",toJson (findFilterWork (groups t) (groups t)))])

#eval do
  let t := (fromTree (fun x : Nat => x) [] (.leaf 0))
  let g : Group := ⟨[],[0],0⟩
  let r := meterAttempt (fun _ _ _ => ⟨⟨[],[],0,0,1⟩,1,0,1⟩) t [] [] g
  emitReview "attempt-root-refusal-cost" (jReceipt r.receipt) (Json.mkObj [("work",toJson (r.work)),("prunedCalls",toJson (r.prunedCalls))])

#eval do
  let t := (normalize (fromTree (fun x : Nat => if x = 0 then 0 else if x = 1 then 0 else if x = 2 then 1 else 0) [] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))))
  let g : Group := ⟨[false],[0,1],0⟩
  let r := meterAttempt (fun _ _ _ => ⟨⟨[],[],0,0,1⟩,1,0,1⟩) t [] [[false]] g
  emitReview "attempt-duplicate-refusal-cost" (jReceipt r.receipt) (Json.mkObj [("work",toJson (r.work)),("prunedCalls",toJson (r.prunedCalls))])

#eval do
  let t := (fromTree (fun x : Nat => x) [true] (.leaf 2))
  let g : Group := ⟨[true],[2],2⟩
  let r := meterAttempt (fun _ _ _ => ⟨⟨[],[],0,0,1⟩,1,0,1⟩) t [] [] g
  emitReview "attempt-entire-refusal-cost" (jReceipt r.receipt) (Json.mkObj [("work",toJson (r.work)),("prunedCalls",toJson (r.prunedCalls))])

#eval do
  let t := (fromTree (fun x : Nat => x) [] (.node (.leaf 0) (.leaf 1)))
  let g : Group := ⟨[false],[0],0⟩
  let r := meterAttempt (fun _ _ _ => ⟨⟨[],[],0,0,1⟩,1,0,1⟩) t [] [] g
  emitReview "attempt-prune-still-pays-local-erase" (jReceipt r.receipt) (Json.mkObj [("work",toJson (r.work)),("prunedCalls",toJson (r.prunedCalls))])

#eval do
  let t := (fromTree (fun x : Nat => x) [] (.node (.leaf 0) (.leaf 1)))
  let r := meterRun 0 t [] []
  emitReview "run-zero-budget-local-work" (jReceipt r.receipt) (Json.mkObj [("work",toJson (r.work)),("copied",toJson (r.copied)),("prunedCalls",toJson (r.prunedCalls))])

#eval do
  let t : Tree := (.node (.leaf 0) (.leaf 1))
  let r := meterGenerate t (fun x : Nat => x) 0
  emitReview "generate-zero-budget-initial-check-and-colors" (jReceipt r.measured.receipt) (Json.mkObj [("work",toJson (r.measured.work)),("copied",toJson (r.measured.copied)),("prunedCalls",toJson (r.measured.prunedCalls)),("oracleCalls",toJson (r.oracleCalls)),("initialCharge",toJson (initialCharge t)),("N",toJson (treeNodes t)),("B",toJson (min 0 ((leaves t).length-1)))])

#eval do
  let t : Tree := (.node (.leaf 7) (.leaf 7))
  let r := meterGenerate t (fun x : Nat => x) 3
  emitReview "duplicate-input-pays-check-but-not-colors" (jReceipt r.measured.receipt) (Json.mkObj [("work",toJson (r.measured.work)),("copied",toJson (r.measured.copied)),("prunedCalls",toJson (r.measured.prunedCalls)),("oracleCalls",toJson (r.oracleCalls)),("initialCharge",toJson (initialCharge t)),("N",toJson (treeNodes t)),("B",toJson (min 3 ((leaves t).length-1)))])

#eval do
  let t : Tree := (.node (.leaf 0) (.leaf 1))
  let r := meterGenerate t (fun x : Nat => x) 9
  emitReview "generate-finish-materializes-output" (jReceipt r.measured.receipt) (Json.mkObj [("work",toJson (r.measured.work)),("copied",toJson (r.measured.copied)),("prunedCalls",toJson (r.measured.prunedCalls)),("oracleCalls",toJson (r.oracleCalls)),("initialCharge",toJson (initialCharge t)),("N",toJson (treeNodes t)),("B",toJson (min 9 ((leaves t).length-1)))])

#eval do
  let t : Tree := (.node (.leaf 0) (.leaf 1))
  let r := meterGenerate t (fun x : Nat => x) 340282366920938463463374607431768211456
  emitReview "oversized-budget-bit-width-survives-clipping" (jReceipt r.measured.receipt) (Json.mkObj [("work",toJson (r.measured.work)),("copied",toJson (r.measured.copied)),("prunedCalls",toJson (r.measured.prunedCalls)),("oracleCalls",toJson (r.oracleCalls)),("initialCharge",toJson (initialCharge t)),("N",toJson (treeNodes t)),("B",toJson (min 340282366920938463463374607431768211456 ((leaves t).length-1)))])

#eval do
  let t : Tree := (.node (.leaf 0) (.leaf 340282366920938463463374607431768211456))
  let r := meterGenerate t (fun x : Nat => x) 1
  emitReview "encoded-labels-and-oracle-tariff" (jReceipt r.measured.receipt) (Json.mkObj [("work",toJson (r.measured.work)),("copied",toJson (r.measured.copied)),("prunedCalls",toJson (r.measured.prunedCalls)),("oracleCalls",toJson (r.oracleCalls)),("initialCharge",toJson (initialCharge t)),("N",toJson (treeNodes t)),("B",toJson (min 1 ((leaves t).length-1)))])

#eval do
  let t := (fromTree (fun x : Nat => if x = 0 then 0 else if x = 1 then 1 else if x = 2 then 0 else if x = 3 then 1 else 0) [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))))
  let r := meterRun 0 t [] []
  emitReview "two-pruned-children-still-join-receipts" (jReceipt r.receipt) (Json.mkObj [("work",toJson (r.work)),("copied",toJson (r.copied)),("prunedCalls",toJson (r.prunedCalls))])

#eval do
  let t : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))
  let r := meterGenerate t (fun x : Nat => if x = 0 then 0 else if x = 1 then 1 else if x = 2 then 0 else if x = 3 then 1 else 0) 2
  emitReview "two-output-source-run-joins-left-output-record" (jReceipt r.measured.receipt) (Json.mkObj [("work",toJson (r.measured.work)),("copied",toJson (r.measured.copied)),("prunedCalls",toJson (r.measured.prunedCalls)),("oracleCalls",toJson (r.oracleCalls)),("initialCharge",toJson (initialCharge t)),("N",toJson (treeNodes t)),("B",toJson (min 2 ((leaves t).length-1)))])

#eval do
  let t : Tree := (.node (.leaf 0) (.leaf 1))
  let r := meterGenerate t (fun _ : Nat => 340282366920938463463374607431768211456) 0
  emitReview "large-color-value-is-not-small-label-width" (jReceipt r.measured.receipt) (Json.mkObj [("work",toJson (r.measured.work)),("copied",toJson (r.measured.copied)),("prunedCalls",toJson (r.measured.prunedCalls)),("oracleCalls",toJson (r.oracleCalls)),("initialCharge",toJson (initialCharge t)),("N",toJson (treeNodes t)),("B",toJson (min 0 ((leaves t).length-1)))])
