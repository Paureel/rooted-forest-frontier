import FastExact
import Lean
open Lean RMAF
partial def reviewForestTree (j : Json) : Except String Tree := do
  match j with
  | .num _ => return .leaf (← j.getNat?)
  | .arr a =>
    if a.size != 2 then throw "binary tree required"
    return .node (← reviewForestTree a[0]!) (← reviewForestTree a[1]!)
  | _ => throw "Nat leaf required"
def reviewForestRow (j : Json) : Except String Json := do
  let id ← (← j.getObjVal? "id").getStr?
  let tj ← j.getObjVal? "a"
  let target ← if tj == Json.null then pure none else (reviewForestTree tj).map some
  let ss ← (← (← j.getObjVal? "b").getArr?).toList.mapM reviewForestTree
  let q ← (← j.getObjVal? "q").getNat?
  let result := GenericForest.solve (fun t s r => OrdinaryDispatch.FastOrdinary.solve r t s) target ss q
  return Json.mkObj [("id",toJson id),("proper",toJson (ForestState.proper target ss)),
    ("forest",toJson result),("agrees",toJson (result.map (ForestState.agrees target ss)))]
def main (args : List String) : IO UInt32 := do
  let raw ← IO.FS.readFile args[0]!
  let stdout ← IO.getStdout
  for line in raw.splitOn "\n" do
    if line.isEmpty then continue
    match Json.parse line >>= reviewForestRow with
    | .ok row => stdout.putStrLn row.compress
    | .error e => throw (IO.userError e)
  return 0
