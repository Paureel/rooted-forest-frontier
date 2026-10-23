import ProducerAudit
open Lean Elab Command IndependentProducer
run_cmd do
  let a := Expr.lam `x (mkConst `Nat) (.bvar 0) .default
  let b := Expr.lam `y (mkConst `Nat) (.bvar 0) .default
  let .ok (_,s) := (encode (.app a b)).run {} | throwError "DAG construction failed"
  unless s.nodes.size == 5 do throwError "binder names coalesced: {s.nodes.size}"
  let c := Expr.lam `x (mkConst `Nat) (.bvar 0) .implicit
  let .ok (_,t) := (encode (.app a c)).run {} | throwError "DAG construction failed"
  unless t.nodes.size == 5 do throwError "binder annotations coalesced: {t.nodes.size}"
  let md : MData := { entries := [(`synthetic, .ofSyntax .missing)] }
  match expression (.mdata md a) with
  | .ok _ => throwError "unsupported metadata escaped refusal"
  | .error _ => pure ()
  liftIO <| IO.println "DAG-CONTROL PASS binder-names binder-annotations syntax-metadata-refusal"
