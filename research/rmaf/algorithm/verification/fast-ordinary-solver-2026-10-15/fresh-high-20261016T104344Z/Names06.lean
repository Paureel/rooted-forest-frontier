-- One-shot measured allocation-cap pilot; only allowed suffix names, no bodies.
import Lean
open Lean
#eval do
  let env ← importModules #[{module := `Ordinary}] {} (trustLevel := 0)
  env.constants.forM fun n _ => do
    if n.getString! == "proper" then IO.println s!"ALLOWED_NAME {n}"
