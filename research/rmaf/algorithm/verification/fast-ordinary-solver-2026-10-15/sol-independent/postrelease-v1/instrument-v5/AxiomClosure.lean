/- Reviewer-only actual stored-body dependency walk. No axiom cache is used. -/
import Producer
open Lean
def reviewerAxiomClosure : IO Unit := do
  initSearchPath (← findSysroot)
  let some moduleText ← IO.getEnv "REVIEW_CLOSURE_MODULE" | throw (IO.userError "exact module required")
  let some rootText ← IO.getEnv "REVIEW_CLOSURE_ROOTS" | throw (IO.userError "exact roots required")
  let roots := (rootText.splitOn "|").map String.toName
  let env ← importModules #[{module := moduleText.toName}] {} (trustLevel := 0)
    (loadExts := false) (level := .private)
  let stdout ← IO.getStdout
  stdout.putStrLn (Json.mkObj [("record",js "root-set"),("module",js moduleText),
    ("roots",toJson (roots.map Name.toString)),("actual_values",toJson true)]).compress
  let mut todo := roots
  let mut seen : Std.HashSet Name := {}
  let mut axioms : List Name := []
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.checked.get.find? n | throw (IO.userError s!"unknown actual declaration {n}")
    let refs := uniq (actualRefs ci.type ++ (ci.value? true |>.map actualRefs |>.getD []) ++ extraRefs ci)
    if ci.isAxiom then axioms := n :: axioms
    stdout.putStrLn (Json.mkObj [("record",js "actual-dependency"),("name",js n.toString),
      ("module",js (moduleOf env n)),("kind",js (kind ci)),("unsafe",toJson ci.isUnsafe),
      ("partial",toJson ci.isPartial),("refs",toJson (refs.map Name.toString)),
      ("body_nodes",toJson (ci.value? true |>.map actualNodes |>.getD 0))]).compress
    todo := refs ++ todo
  stdout.putStrLn (Json.mkObj [("record",js "actual-axiom-closure"),("declarations",toJson seen.size),
    ("axioms",toJson ((uniq axioms).map Name.toString)),
    ("cached_axiom_extension_used",toJson false)]).compress
#eval reviewerAxiomClosure
