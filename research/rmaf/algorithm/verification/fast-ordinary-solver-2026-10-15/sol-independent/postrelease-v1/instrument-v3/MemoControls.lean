import Producer
open Lean
def shared (depth : Nat) (leaf : Expr) : Expr :=
  match depth with
  | 0 => leaf
  | n+1 => let sub := shared n leaf; .app sub sub
def memoResult : Json := Id.run do
  let a := mkConst `Synthetic.A
  let b := mkConst `Synthetic.B
  let big := shared 30 a
  return Json.mkObj [
    ("depth5_nodes",toJson (actualNodes (shared 5 a))),
    ("depth30_nodes",toJson (actualNodes big)),
    ("right_extra_nodes",toJson (actualNodes (.app big b))),
    ("metadata_alias_nodes",toJson (actualNodes (.app (.mdata {} a) a))),
    ("refs_balanced",toJson ((uniq (actualRefs big)).map Name.toString)),
    ("refs_right_extra",toJson ((uniq (actualRefs (.app big b))).map Name.toString))]
#eval IO.println memoResult.compress
