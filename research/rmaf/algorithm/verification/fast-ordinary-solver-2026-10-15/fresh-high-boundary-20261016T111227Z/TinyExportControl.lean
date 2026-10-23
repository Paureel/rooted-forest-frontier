-- Administrative serializer control, not a theorem about source geometry.
-- Uses installed Lean CompactedRegion directly, preserving shared objects.
import Lean
open Lean
unsafe def exportControl : IO Unit := do
  IO.FS.createDirAll "exports"
  let mut e : Expr := .app (.const `Nat.succ []) (.lit (.natVal 0))
  for _ in [0:20] do e := .app e e
  let name := Name.num (.str .anonymous "literal.dot") 7
  let metadata := MData.empty.insert `testString (.ofString "control")
    |>.insert `testNat (.ofNat 7)
    |>.insert `testSyntax (.ofSyntax (.atom .none "exact-syntax"))
  let wrapped := Expr.mdata metadata (.letE name (.const `Nat []) e (.bvar 0) true)
  let payload : Nat × Array (Name × Expr) := (20, #[(name,e), (`wrapped,wrapped)])
  let _ ← CompactedRegion.save "exports/control-v1.olean" `OwnHighExportControl payload #[] none
  let (restored, _region) ← CompactedRegion.read (α := Nat × Array (Name × Expr)) "exports/control-v1.olean" #[]
  unless payload.1 == restored.1 && payload.2.size == restored.2.size do
    throw (IO.userError "control payload header mismatch")
  for i in [:payload.2.size] do
    unless payload.2[i]!.1 == restored.2[i]!.1 && Expr.equal payload.2[i]!.2 restored.2[i]!.2 do
      throw (IO.userError "control exact structural roundtrip mismatch")
  let bytes ← IO.FS.readBinFile "exports/control-v1.olean"
  unless bytes.size < 65536 do throw (IO.userError "sharing was not retained in bounded control")
  IO.println ((Json.mkObj [("kind",toJson "native-dag-control"),("roundtrip",toJson true),
    ("depth",toJson (20 : Nat)),("raw_bytes",toJson bytes.size),
    ("numeric_name_and_syntax_metadata",toJson true)]).compress)
#eval exportControl
