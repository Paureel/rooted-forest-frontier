import Lean
open Lean
namespace BoundedExprDAG
/- Author audit instrumentation. ExprStructMap preserves binder names and
annotations. Each expression node is emitted once with backward child ids.
Neither Expr.toString nor a recursively expanded expression repr is used. -/
structure Sink where
 dir : System.FilePath
 stem : String
 chunk : Nat:=0
 bytes : Nat:=0
 total : Nat:=0
 nodes : Nat:=0
 memo : ExprStructMap Nat:={}
 deriving Inhabited
abbrev Dump := StateRefT Sink IO
def chunkLimit : Nat:=4*1024*1024
def totalLimit : Nat:=16*1024*1024
def path (s : Sink) : System.FilePath:=s.dir/(s.stem++"-"++toString s.chunk++".jsonl")
def emit (j : Json) : Dump Unit:=do
 let line:=j.compress++"\n"
 let len:=line.utf8ByteSize
 if len>chunkLimit then throw <| IO.userError "DAG_LINE_CAP"
 let s←get
 if s.total+len>totalLimit then throw <| IO.userError "DAG_RAW_TOTAL_CAP"
 let s:=if s.bytes+len>chunkLimit then {s with chunk:=s.chunk+1,bytes:=0} else s
 let h←IO.FS.Handle.mk (path s) .append
 h.putStr line
 set {s with bytes:=s.bytes+len,total:=s.total+len}
def boundedRepr {α : Type} [Repr α] (x : α) : IO String:=do
 let s:=reprStr x
 if s.utf8ByteSize>1024*1024 then throw <| IO.userError "DAG_ATOMIC_FIELD_CAP"
 return s
partial def syntaxCount (s : Syntax) (fuel : Nat) : Bool:=
 if fuel=0 then false else match s with
 | .node _ _ args=>args.all (fun s=>syntaxCount s (fuel-1)) && args.size≤8192
 | _=>true
def metadata (m : MData) : IO Json:=do
 let mut a:=#[]
 for (k,v) in m.entries do
  if let .ofSyntax s:=v then
   unless syntaxCount s 128 do throw <| IO.userError "DAG_METADATA_SYNTAX_CAP"
  a:=a.push (toJson (←boundedRepr k,←boundedRepr v))
 return .arr a
partial def level (l : Level) (fuel : Nat:=128) : IO Json:=do
 if fuel=0 then throw <| IO.userError "DAG_LEVEL_DEPTH_CAP"
 match l with
 | .zero=>return toJson (["zero"]:List String)
 | .succ a=>return .arr #[toJson "succ",←level a (fuel-1)]
 | .max a b=>return .arr #[toJson "max",←level a (fuel-1),←level b (fuel-1)]
 | .imax a b=>return .arr #[toJson "imax",←level a (fuel-1),←level b (fuel-1)]
 | .param n=>return .arr #[toJson "param",toJson (←boundedRepr n)]
 | .mvar n=>return .arr #[toJson "mvar",toJson (←boundedRepr n)]
partial def expr (e : Expr) : Dump Nat:=do
 if let some n:=(←get).memo[(⟨e⟩:ExprStructEq)]? then return n
 let (tag,fields,children)←match e with
 | .bvar n=>pure ("bvar",toJson n,#[])
 | .fvar n=>pure ("fvar",toJson (←boundedRepr n),#[])
 | .mvar n=>pure ("mvar",toJson (←boundedRepr n),#[])
 | .sort l=>pure ("sort",←level l,#[])
 | .const n ls=>do
   let levels←ls.toArray.mapM (fun l=>level l)
   pure ("const",Json.arr #[toJson (←boundedRepr n),Json.arr levels],#[])
 | .app f a=>pure ("app",Json.null,#[←expr f,←expr a])
 | .lam n t b bi=>pure ("lam",toJson (←boundedRepr n,←boundedRepr bi),#[←expr t,←expr b])
 | .forallE n t b bi=>pure ("forall",toJson (←boundedRepr n,←boundedRepr bi),#[←expr t,←expr b])
 | .letE n t v b nd=>pure ("let",toJson (←boundedRepr n,nd),#[←expr t,←expr v,←expr b])
 | .lit l=>pure ("lit",toJson (←boundedRepr l),#[])
 | .mdata m a=>pure ("mdata",←metadata m,#[←expr a])
 | .proj n i a=>pure ("proj",toJson (←boundedRepr n,i),#[←expr a])
 let s←get
 if s.nodes≥1000000 then throw <| IO.userError "DAG_NODE_CAP"
 let id:=s.nodes
 emit <| Json.mkObj [("record",toJson "node"),("id",toJson id),("tag",toJson tag),
  ("fields",fields),("children",toJson children)]
 modify fun s=>{s with nodes:=id+1,memo:=s.memo.insert e id}
 return id
def kind : ConstantInfo→String
 | .axiomInfo _=>"axiom" | .defnInfo _=>"definition" | .thmInfo _=>"theorem"
 | .opaqueInfo _=>"opaque" | .quotInfo _=>"quotient" | .ctorInfo _=>"constructor"
 | .recInfo _=>"recursor" | .inductInfo _=>"inductive"
end BoundedExprDAG
