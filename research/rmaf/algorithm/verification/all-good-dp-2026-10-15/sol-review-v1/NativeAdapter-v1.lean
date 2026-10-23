import ExactMinimum
import Lean
open RMAF ForestState AllGoodDP Lean
namespace SolNative
def js (s : String) : Json := toJson s
def treeJson : Tree → Json
  | .leaf x => toJson x
  | .node l r => Json.arr #[treeJson l,treeJson r]
def optionTree (t : Option Tree) : Json := match t with | none => Json.null | some t => treeJson t
def paintVertices (a : String) : Paint → List Json
  | .leaf x c => [Json.mkObj [("address",js a),("color",toJson c),("leaf",toJson x)]]
  | .node c l r => Json.mkObj [("address",js a),("color",toJson c),("leaf",Json.null)] ::
      (paintVertices (a++"0") l ++ paintVertices (a++"1") r)
def rows (cs : List Nat) (own : Nat → Nat) (a : String) : Tree → List Json
  | .leaf _ => []
  | .node l r =>
      Json.mkObj [("address",js a),("candidates",toJson ((table cs own (.node l r)).map
        (fun p => Json.mkObj [("color",toJson (root p)),("changes",toJson (changes p))])))] ::
        (rows cs own (a++"0") l ++ rows cs own (a++"1") r)
def paintRecord (T : Option Tree) (ss : List Tree) : Json :=
  match T with
  | none => Json.null
  | some t =>
      let p := solve (List.range ss.length) (owner ss) t
      Json.mkObj [("vertices",toJson (paintVertices "" p)),("changes",toJson (changes p)),
        ("rawBlocks",toJson (rawBlocks p)),("blocks",toJson (blocks p)),
        ("rows",toJson (rows (List.range ss.length) (owner ss) "" t)),
        ("coarseVisits",toJson (visits ss.length t)),("treeVertices",toJson (vertices t))]
def stateRecord (tag : String) (T : Option Tree) (ss : List Tree) (qs : List Nat) : Json :=
  let out := AllGoodDP.run T ss
  Json.mkObj [("id",js tag),("proper",toJson (proper T ss)),("allGood",toJson (allGood T ss)),
    ("run",match out with | none => Json.null | some f => toJson f),
    ("acceptedAgrees",match out with | none => Json.null | some f => toJson (agrees T ss f)),
    ("cost",match out with | none => Json.null | some f => toJson (additionalCost ss f)),
    ("decisions",toJson (qs.map (decideBudget T ss))),
    ("owners",toJson ((labels T).map (fun x => Json.arr #[toJson x,toJson (owner ss x)]))),
    ("paint",if allGood T ss then paintRecord T ss else Json.null)]
def forestRecord (tag : String) (T : Option Tree) (ss : List Tree) (F : List (List Nat)) : Json :=
  Json.mkObj [("id",js tag),("F",toJson F),("agrees",toJson (agrees T ss F)),
    ("costNat",toJson (additionalCost ss F)),("sourceCount",toJson ss.length),("blockCount",toJson F.length),
    ("targetEmbeddings",toJson (targetEmbeddings T F)),
    ("sourceChecks",toJson (ss.map (sourceCheck T F)))]
def geometryRecord (tag : String) (t : Tree) (B : List Nat) : Json :=
  Json.mkObj [("id",js tag),("hull",toJson ((minimalVertices B t).map
    (fun a => String.ofList (a.map (fun b => if b then '1' else '0'))))),
    ("restriction",optionTree (restrict B t))]
def emit (tag : String) (j : Json) : IO Unit := IO.println (tag++"\t"++j.compress)
end SolNative
