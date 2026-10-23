import DAGControlOne
import BoundedExprDAG
open Lean Elab Command BoundedExprDAG
run_cmd do
 let env←getEnv
 let producer:Name:=`DAGControlOne
 let some idx:=env.header.moduleNames.toList.idxOf? producer | throwError "DAG_PRODUCER_NOT_IMPORTED"
 let data:=env.header.moduleData[idx]!
 unless data.constants.size=data.constNames.size do throwError "DAG_PRODUCER_ARRAY_MISMATCH"
 unless 1≤data.constants.size do throwError "DAG_RANGE_MISMATCH"
 let mut metadataRows:Array (Nat×ConstantInfo×List (String×Json)):=#[]
 let mut rejects:=0
 for j in [0:1] do
  let ci:=data.constants[j]!
  let stored:=data.constNames[j]!
  unless stored=ci.name do throwError "DAG_PRODUCER_NAME_MISMATCH"
  let refs:=ci.getUsedConstantsAsSet.toList
  let mut ax:List Name:=if ci.isAxiom then [ci.name] else []
  for n in refs do ax:=ax++(←collectAxioms n).toList
  ax:=ax.eraseDups
  if (ci.isAxiom && !([`propext,`Quot.sound,`Classical.choice]:List Name).contains ci.name) ||
    ax.any (fun n=>!([`propext,`Quot.sound,`Classical.choice]:List Name).contains n) then rejects:=rejects+1
  let resolved:=match env.getModuleIdxFor? ci.name with
   | some k=>env.header.moduleNames[k.toNat]!.toString | none=>"<unresolved>"
  metadataRows:=metadataRows.push (j,ci,[("record",toJson "declaration"),("producer",toJson producer.toString),
   ("index",toJson j),("stored_name",toJson stored.toString),("actual_name",toJson ci.name.toString),
   ("resolved_origin",toJson resolved),("kind",toJson (kind ci)),
   ("has_body",toJson (ci.value? true).isSome),("direct_references",toJson (refs.map Name.toString)),
   ("axiom_references",toJson (ax.map Name.toString)),("level_params",toJson (ci.levelParams.map (fun n=>reprStr n)))])
 let action:Dump Unit:=do
  emit <| Json.mkObj [("record",toJson "header"),("producer",toJson producer.toString),
   ("count",toJson data.constants.size),("start",toJson (0:Nat)),("end",toJson (1:Nat))]
  for (_,ci,fields) in metadataRows do
   let ty←expr ci.type
   let body : Option Nat ← match ci.value? true with
    | none=>pure none
    | some e=>do let r←expr e;pure (some r)
   emit <| Json.mkObj (fields++[("type_root",toJson ty),("body_root",toJson body)])
  let s←get
  emit <| Json.mkObj [("record",toJson "footer"),("declarations",toJson metadataRows.size),
   ("nodes",toJson s.nodes),("bytes_before_footer",toJson s.total),("rejects",toJson rejects)]
 let (_,sink)←liftIO <| action.run {dir:="/Users/paurel/Documents/ChatGPT/bootscience/results/algorithm-universal233-hard2-scheduler-20261016T112422Z-20261016T112613901387Z/dag-controls-v2/records-One",stem:="dag"}
 logInfo m!"DAG_DUMP|{producer}|{metadataRows.size}|{sink.nodes}|{sink.total}"
 if rejects>0 then throwError "DAG_CUSTOM_AXIOM_REJECTED"
