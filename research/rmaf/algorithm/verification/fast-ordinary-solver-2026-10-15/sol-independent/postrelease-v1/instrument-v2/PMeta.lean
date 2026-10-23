import Lean
open Lean Elab Command
elab "install_review_metadata" : command => do
  liftCoreM do
    let md : MData := {entries := [
      (`strK, .ofString "literal\nquotes\" λ"),
      (`boolK, .ofBool true),
      (`nameK, .ofName (.str (.num (.str .anonymous "deep") 7) "tail")),
      (`natK, .ofNat 18446744073709551625),
      (`intK, .ofInt (-19))]}
    addDecl <| .defnDecl {
      name := `ReviewMetadata.positive
      levelParams := []
      type := mkConst ``Nat
      value := .mdata md (.lit (.natVal 37))
      hints := .opaque
      safety := .safe }
    let bad : MData := { entries := [(`syntaxK, .ofSyntax (.atom .none "literal-syntax"))] }
    addDecl <| .defnDecl {
      name := `ReviewMetadata.unsupportedSyntax
      levelParams := []
      type := mkConst ``Nat
      value := .mdata bad (.lit (.natVal 37))
      hints := .opaque
      safety := .safe }
install_review_metadata
