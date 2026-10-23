import CompletionConsumers
import Consumers
import Lean
open Lean RMAF ForestState
namespace SolNativeExtra
def jTree : Tree → Json
  | .leaf x => toJson x
  | .node l r => Json.arr #[jTree l,jTree r]
def jOpt : Option Tree → Json
  | none => Json.null
  | some t => jTree t
def jTrees (ss : List Tree) : Json := Json.arr (ss.map jTree).toArray
def O : Tree := .node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
def SS : List Tree := [.leaf 2,.node (.leaf 0) (.leaf 1)]
def FF : List (List Nat) := [[2],[1,0]]
def CT := cleanupTarget (some O) 2
def CS := cleanupSources SS 2
def CF := cleanupForest FF 2
def QT := CT.map (contract 0 1 3)
def QS := CS.map (contract 0 1 3)
def QF := CF.map (contractBlock 0 1 3)
def ET := QT.map (expand 0 1 3)
def ES := QS.map (expand 0 1 3)
def EF := QF.map (expandBlock 0 1 3)
def RF : List (List Nat) := [2] :: EF
def C : Tree := .node (.leaf 0) (.leaf 1)
def Deep : Tree := .node (.node C (.leaf 2)) (.leaf 3)
def hull := (minimalVertices [0,2] Deep).map (fun v => String.ofList (v.map (fun b => if b then '1' else '0')))
#check @ForestState.singleton_cleanup_forward
#check @ForestState.singleton_cleanup_reverse

#eval IO.println (Json.mkObj [("cleanup", Json.mkObj [("T", jOpt CT), ("ss", jTrees CS), ("F", toJson CF), ("cost", toJson (additionalCost CS CF)), ("valid", toJson (agrees CT CS CF))]), ("contract", Json.mkObj [("T", jOpt QT), ("ss", jTrees QS), ("F", toJson QF), ("cost", toJson (additionalCost QS QF)), ("valid", toJson (agrees QT QS QF))]), ("expand", Json.mkObj [("T", jOpt ET), ("ss", jTrees ES), ("F", toJson EF), ("cost", toJson (additionalCost ES EF)), ("valid", toJson (agrees ET ES EF))]), ("reconstructedF", toJson RF), ("reconstructedCost", toJson (additionalCost SS RF)), ("reconstructedValid", toJson (agrees (some O) SS RF)), ("nullValid", toJson (agrees none [] [])), ("nullCost", toJson (additionalCost [] [])), ("mutations", Json.arr #[Json.mkObj [("id", Json.str "hull-unary-erasure"), ("clean", toJson hull), ("corrupt", toJson (hull.filter (fun s => s != "00")))], Json.mkObj [("id", Json.str "source-cost-minus-one"), ("clean", toJson (additionalCost SS FF)), ("corrupt", toJson (FF.length - 1))], Json.mkObj [("id", Json.str "omit-reverse-direction"), ("clean", toJson (["forward","reverse"] : List String)), ("corrupt", toJson (["forward"] : List String))], Json.mkObj [("id", Json.str "fabricated-reconstruction"), ("clean", toJson (agrees (some (.leaf 0)) [.leaf 0] [[0]])), ("corrupt", toJson (agrees (some (.leaf 0)) [.leaf 0] []))], Json.mkObj [("id", Json.str "missing-component-readiness"), ("clean", toJson (cherryReady (some C) [.leaf 0,.leaf 1] 0 1 2)), ("corrupt", toJson (cherry 0 1 C))], Json.mkObj [("id", Json.str "accept-nonfresh-z"), ("clean", toJson (cherryReady (some C) [C] 0 1 1)), ("corrupt", toJson (proper (some C) [C] && cherry 0 1 C))], Json.mkObj [("id", Json.str "drop-surviving-label"), ("clean", toJson (leaves (contract 0 1 3 O))), ("corrupt", toJson (leaves (.leaf 3)))], Json.mkObj [("id", Json.str "weak-endpoint-clearance"), ("clean", toJson (disjointVertices (minimalVertices [0,1] C) (minimalVertices [1] C))), ("corrupt", toJson (disjointVertices (minimalVertices [0] C) (minimalVertices [1] C)))], Json.mkObj [("id", Json.str "reassignment-cost-equality"), ("clean", toJson (decide (additionalCost [C] (reassignedForest [[0],[1]] [0] 1) = additionalCost [C] [[0],[1]]))), ("corrupt", toJson true)], Json.mkObj [("id", Json.str "duplicate-state-labels"), ("clean", toJson (proper (some (.node (.leaf 0) (.leaf 0))) [.leaf 0,.leaf 0])), ("corrupt", toJson true)]])]).compress
end SolNativeExtra
