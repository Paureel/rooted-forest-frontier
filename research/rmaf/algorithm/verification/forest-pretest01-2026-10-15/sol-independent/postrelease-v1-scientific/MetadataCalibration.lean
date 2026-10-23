import PostreleaseProducerAuditV2
open Lean Elab Command IndependentProducer
run_cmd do
  let text := "retained-source"
  let raw : Substring.Raw := ⟨text,⟨1⟩,⟨5⟩⟩
  let orig : SourceInfo := .original raw ⟨3⟩ raw ⟨8⟩
  let id : Syntax := .ident orig raw `Plant.value [.namespace `Plant,.decl `Plant.value ["field"]]
  let stx : Syntax := .node .none `nodeKind #[.missing,.atom (.synthetic ⟨2⟩ ⟨7⟩ true) "atom",id]
  let md : MData := { entries := [(`synthetic,.ofSyntax stx)] }
  let e := Expr.mdata md (mkConst `Nat)
  let .ok (root,s) := (encode e).run {} | throwError "lossless metadata encoding failed"
  unless s.strings == #[text] do throwError "source string table lost or duplicated"
  unless root == 1 && s.nodes.size == 2 do throwError "metadata/body nodes lost"
  let .ok recorded := expression e | throwError "expression record failed"
  liftIO <| IO.println ("METADATA-CONTROL " ++ recorded.compress)
  let a := Expr.lam `x (mkConst `Nat) (.bvar 0) .default
  let b := Expr.lam `y (mkConst `Nat) (.bvar 0) .implicit
  let .ok (_,t) := (encode (.app a b)).run {} | throwError "structural DAG failed"
  unless t.nodes.size == 5 do throwError "binder structure lost after metadata extension"
  liftIO <| IO.println "METADATA-CONTROL PASS source-info substring prereferences all-syntax binder-structure"
