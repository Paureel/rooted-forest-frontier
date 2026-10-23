import NativeAdapter
open Lean RMAF ForestState AllGoodDP SolNative RestrictionBridge
namespace SolGeometry
def blocksGeometry (t : Tree) (F : List (List Nat)) : Json :=
  toJson (F.map (fun B => Json.mkObj [("B",toJson B),
    ("hull",toJson ((minimalVertices B t).map (fun a => String.ofList (a.map (fun b => if b then '1' else '0'))))),
    ("restriction",optionTree (restrict B t))]))
def record (tag : String) (T : Option Tree) (ss : List Tree) (F : List (List Nat)) : Json :=
  Json.mkObj [("id",js tag),("F",toJson F),
    ("target",match T with | none => toJson ([] : List Json) | some t => blocksGeometry t F),
    ("targetEmbeddings",toJson (targetEmbeddings T F)),
    ("refines",toJson (F.all (fun B => ss.any (fun s => contained B (leaves s))))),
    ("componentTopology",toJson (F.all (fun B => ss.any (fun s => contained B (leaves s) && targetAgrees T s B)))),
    ("sources",toJson (ss.map (fun s => Json.mkObj [("labels",toJson (leaves s)),
      ("family",toJson (family (leaves s) F)),("geometry",blocksGeometry s (family (leaves s) F)),
      ("embeddings",toJson (pairwiseEmbeddings s (family (leaves s) F)))])))]
end SolGeometry
