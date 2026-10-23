import RAHostile
import Lean

open Lean Elab Command
structure DAG where
 memo : Std.HashMap Expr Nat := {}
 nodes : Array Json := #[]
partial def exprDAG (e : Expr) (s : DAG) : Except String (Nat×DAG) := do
 if let some i:=s.memo[e]? then return (i,s)
 if s.nodes.size>=32768 then throw "EXPR_DAG_NODE_CAP"
 let (tag,payload,children) : String×Json×Array Expr := match e with
 | .bvar n=>("bvar",toJson n,#[])
 | .fvar n=>("fvar",toJson n.name.toString,#[])
 | .mvar n=>("mvar",toJson n.name.toString,#[])
 | .sort l=>("sort",toJson (reprStr l),#[])
 | .const n ls=>("const",Json.mkObj [("name",toJson n.toString),("levels",toJson (ls.map reprStr))],#[])
 | .app a b=>("app",Json.null,#[a,b])
 | .lam n a b bi=>("lam",toJson (n.toString,reprStr bi),#[a,b])
 | .forallE n a b bi=>("forall",toJson (n.toString,reprStr bi),#[a,b])
 | .letE n a b c nd=>("let",toJson (n.toString,nd),#[a,b,c])
 | .lit v=>("lit",toJson (reprStr v),#[])
 | .mdata md a=>("mdata",toJson (reprStr md),#[a])
 | .proj n i a=>("proj",toJson (n.toString,i),#[a])
 if payload.compress.utf8ByteSize>65536 then throw "NODE_PAYLOAD_CAP"
 let mut state:=s
 let mut edges : Array Nat:=#[]
 for child in children do
  let (i,t)←exprDAG child state
  state:=t;edges:=edges.push i
 let idx:=state.nodes.size
 let node:=Json.mkObj [("tag",toJson tag),("payload",payload),("children",toJson edges)]
 let result: DAG:=⟨state.memo.insert e idx,state.nodes.push node⟩
 return (idx,result)
def exportedDAG (e : Expr) : Except String Json := do
 let (root,s)←exprDAG e {}
 return Json.mkObj [("root",toJson root),("nodes",toJson s.nodes)]

set_option maxRecDepth 4000
run_cmd do
 let env←getEnv
 let wanted : List Name := [`RAHostile]
 let allowed : List Name := [`Classical.choice,`Quot.sound,`propext]
 let mut counts : Array Json:=#[]
 let mut bad : Array Json:=#[]
 for i in [:env.header.moduleNames.size] do
  let producer:=env.header.moduleNames[i]!
  if wanted.contains producer then
   let data:=env.header.moduleData[i]!
   unless data.constants.size==data.constNames.size do throwError "PRODUCER_ARRAY_LENGTH_MISMATCH"
   let path←liftIO <| findOLean producer
   counts:=counts.push (Json.mkObj [("producer",toJson producer.toString),("count",toJson data.constants.size),("path",toJson path.toString)])
   for j in [:data.constants.size] do
    let ci:=data.constants[j]!
    unless data.constNames[j]! == ci.name do throwError "PRODUCER_NAME_MISMATCH"
    let kind:=match ci with
     | .axiomInfo _=>"axiom" | .defnInfo _=>"definition" | .thmInfo _=>"theorem"
     | .opaqueInfo _=>"opaque" | .quotInfo _=>"quotient" | .ctorInfo _=>"constructor"
     | .recInfo _=>"recursor" | .inductInfo _=>"inductive"
    let body:=match ci with | .thmInfo _=>none | _=>ci.value? true
    let ty←match exportedDAG ci.type with | .ok d=>pure d | .error e=>throwError e
    let bd←match body with
     | none=>pure Json.null
     | some b=>match exportedDAG b with | .ok d=>pure d | .error e=>throwError e
    let mut refs:=ci.getUsedConstantsAsSet.toList
    if let some e:=body then refs:=refs++e.getUsedConstants.toList
    refs:=refs.eraseDups
    let mut ax : List Name:=[]
    if ci.isAxiom then ax:=[ci.name]
    for n in refs do ax:=ax++(←collectAxioms n).toList
    ax:=ax.eraseDups
    let resolved:=match env.getModuleIdxFor? ci.name with | some k=>env.header.moduleNames[k.toNat]!.toString | none=>"<unresolved>"
    let row:=Json.mkObj [("producer",toJson producer.toString),("index",toJson j),("name",toJson ci.name.toString),("resolved_origin",toJson resolved),("kind",toJson kind),("type_dag",ty),("body_dag",bd),("body_scope",toJson (if kind=="theorem" then "OMITTED_THEOREM_TEXT_FULL_ACTUAL_PROOF_AX_WALK" else "FULL_NONPROOF_DAG")),("references",toJson (refs.map Name.toString)),("axiom_references",toJson (ax.map Name.toString))]
    let payload:=row.compress
    if payload.utf8ByteSize>4194304 then throwError "DAG_CHUNK_CAP"
    let dest:="/Users/paurel/Documents/ChatGPT/bootscience/results/algorithm-universal233-recovery-attempt-20261016T112422Z-20261016T112849760410Z/producer-hostile-v1/"++producer.toString++"-"++toString j++".json.gz"
    let zipped←liftIO <| IO.Process.output {cmd:="/bin/sh",args:=#["-c","exec /usr/bin/gzip -1 -c > "++dest]} (some payload)
    unless zipped.exitCode==0 do throwError "GZIP_SINK_FAILED"
    if (ci.isAxiom && !allowed.contains ci.name) || ax.any (fun n=>!allowed.contains n) then bad:=bad.push (toJson ci.name.toString)
 liftIO <| IO.FS.writeFile "/Users/paurel/Documents/ChatGPT/bootscience/results/algorithm-universal233-recovery-attempt-20261016T112422Z-20261016T112849760410Z/producer-hostile-v1/index.json" (Json.mkObj [("counts",toJson counts),("rejects",toJson bad)]).compress
 if !bad.isEmpty then throwError "REJECT_PRODUCER_OCCURRENCE"
 logInfo m!"BOUNDED_DAG_PRODUCER_PASS|{counts.size}"
