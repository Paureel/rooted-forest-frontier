import RepairDagProducerV3
open Lean
#eval do
 let mut nodes : Array Expr := (List.range 8192).toArray.map (fun n=>mkNatLit n)
 while nodes.size>1 do
  let mut next : Array Expr := #[]
  for i in [:nodes.size/2] do
   next := next.push (.app nodes[2*i]! nodes[2*i+1]!)
  nodes := next
 IO.println (exprDag nodes[0]!).compress
 IO.println ((Json.str (String.ofList (List.replicate (4*1024*1024) 'x'))).boundedCompress)
