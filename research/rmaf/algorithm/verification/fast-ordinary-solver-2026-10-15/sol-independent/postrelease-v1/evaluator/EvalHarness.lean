/- Reviewer-authored JSON adapter; calls the actual released solver unchanged. -/
import FastExact
import Lean
open Lean RMAF

partial def parseTree (j : Json) : Except String Tree := do
  match j with
  | .num _ => return .leaf (← j.getNat?)
  | .arr xs =>
    if xs.size != 2 then throw "tree is not binary"
    return .node (← parseTree xs[0]!) (← parseTree xs[1]!)
  | _ => throw "tree is not a Nat leaf or binary pair"

def member (j : Json) (s : String) : Except String Json := j.getObjVal? s

def answer (j : Json) : Except String Json := do
  let id ← (← member j "id").getStr?
  let a ← parseTree (← member j "a")
  let b ← parseTree (← member j "b")
  let mode ← (← member j "mode").getStr?
  if mode == "agreement" then
    let blocks : List (List Nat) ← fromJson? (← member j "blocks")
    return Json.mkObj [("id",toJson id),("agreement",toJson (RMAF.agreement a b blocks))]
  else
    let k ← (← member j "k").getNat?
    let actual := OrdinaryDispatch.FastOrdinary.external a b k
    let core := OrdinaryDispatch.FastOrdinary.solve (k-1) a b
    return Json.mkObj [
      ("id",toJson id),("proper",toJson (Universal233.DepthOne.proper a b)),
      ("partition",match actual with | none => Json.null | some o => toJson o.partition),
      ("sourceCuts",match actual with | none => Json.null | some o => toJson o.sourceCuts),
      ("core",toJson core)]

def main (args : List String) : IO UInt32 := do
  if args.length != 1 then throw (IO.userError "expected exact own JSONL input path")
  let raw ← IO.FS.readFile args[0]!
  let stdout ← IO.getStdout
  for line in raw.splitOn "\n" do
    if line.isEmpty then continue
    let parsed := Json.parse line >>= answer
    match parsed with
    | .ok row => stdout.putStrLn row.compress
    | .error error =>
      let id := (Json.parse line >>= fun j => member j "id" >>= Json.getStr?).toOption.getD "<invalid>"
      stdout.putStrLn (Json.mkObj [("id",toJson id),("input_error",toJson error)]).compress
  return 0
