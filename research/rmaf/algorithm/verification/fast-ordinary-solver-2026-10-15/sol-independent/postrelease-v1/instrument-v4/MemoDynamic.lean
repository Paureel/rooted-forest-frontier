import Producer
open Lean
def reviewerShared : Nat → Expr → Expr
  | 0, leaf => leaf
  | n+1, leaf => let sub := reviewerShared n leaf; .app sub sub
#eval (do
  let env ← IO.getEnv "REVIEW_MEMO_DEPTH"
  let depth := (env.getD "5").toNat!
  let a := mkConst `Synthetic.A
  let b := mkConst `Synthetic.B
  let big := reviewerShared depth a
  let (count, cache) := (countActualNodes big).run {}
  IO.println (Json.mkObj [
    ("depth",toJson depth),("nodes",toJson count),("cache_entries",toJson cache.size),
    ("right_extra_nodes",toJson (actualNodes (.app big b))),
    ("metadata_alias_nodes",toJson (actualNodes (.app (.mdata {} a) a))),
    ("refs_balanced",toJson ((uniq (actualRefs big)).map Name.toString)),
    ("refs_right_extra",toJson ((uniq (actualRefs (.app big b))).map Name.toString))]).compress : IO Unit)
