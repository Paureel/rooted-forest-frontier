import Lean
import WorkControls
open Lean RMAF VertexGeometry Universal233.CoreProgram Universal233.CoreWork Universal233.WholeSourceMass Universal233.WholeSourceWork
 def ja (v : RMAF.Vertex) : String := String.ofList (v.map (fun b => if b then '1' else '0'))
 def jo (o : Output) : Json := Json.mkObj [("partition",toJson o.partition),("cuts",toJson (o.sourceCuts.map ja))]
 def ownedEmpty : Owned := ⟨[],0,0,0,0⟩
 def jdesc (v w : RMAF.Vertex) (c : Colors) : Json :=
   toJson (([(0,c.a),(1,c.b),(2,c.c)]).filterMap (fun (i,l) => match l with
   | .keep => none
   | .single p => some (toJson [toJson "local",toJson i,toJson (if p=v then "v" else "w")])
   | .joint _ _ => some (toJson [toJson "joint",toJson i,toJson "v",toJson "w"])))
 def reviewEmit (id : String) (value metrics : Json) : IO Unit := IO.println ("WHOLE_VALUE "++(Json.mkObj [("id",toJson id),("value",value),("metrics",metrics)]).compress)


#eval do
  let T : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))
  let c : Colors := (⟨(.single [false]),.keep,.keep⟩ : Colors)
  reviewEmit "actual-local-parent-regions-residues" (toJson (([0,1,2,3] : List Nat).map (fun x => (meterTagged T [0,2] [1] c x).value))) (Json.mkObj [("taggedCap",toJson (taggedCap T [0,2] [1] c))])

#eval do
  let T : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))
  let c : Colors := (⟨(.joint [false] [true]),.keep,.keep⟩ : Colors)
  reviewEmit "joint-sum-encoding-collision-trap" (toJson (([0,2] : List Nat).map (fun x => (meterTagged T [0,2] [1] c x).value))) (Json.mkObj [("taggedCap",toJson (taggedCap T [0,2] [1] c))])

#eval do
  let T : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))
  let c : Colors := (⟨(.joint [false] [true]),.keep,.keep⟩ : Colors)
  reviewEmit "joint-parent-residues-distinct" (toJson (([0,1,2,3] : List Nat).map (fun x => (meterTagged T [0,3] [1] c x).value))) (Json.mkObj [("taggedCap",toJson (taggedCap T [0,3] [1] c))])

#eval do
  let T : Tree := (.leaf 7)
  let c : Colors := (⟨(.single []),.keep,.keep⟩ : Colors)
  reviewEmit "singleton-root-is-removed-label-three" (toJson (([7] : List Nat).map (fun x => (meterTagged T [7] [] c x).value))) (Json.mkObj [("taggedCap",toJson (taggedCap T [7] [] c))])

#eval do
  let T : Tree := (.leaf 0)
  let c : Colors := (⟨(.joint [] []),.keep,.keep⟩ : Colors)
  reviewEmit "joint-full-coordinate-value-versus-cardinality" (toJson (([0,1,2] : List Nat).map (fun x => (meterTagged T [0] [1] c x).value))) (Json.mkObj [("taggedCap",toJson (taggedCap T [0] [1] c))])

#eval do
  let T : Tree := (.leaf 7)
  let c : Colors := (⟨(.single []),.keep,.keep⟩ : Colors)
  reviewEmit "empty-active-parent-costs-membership" (toJson (([7] : List Nat).map (fun x => (meterTagged T [] [7] c x).value))) (Json.mkObj [("taggedCap",toJson (taggedCap T [] [7] c))])

#eval do
  let T : Tree := (.leaf 0)
  let c : Colors := (⟨(.single []),.keep,.keep⟩ : Colors)
  reviewEmit "overlapping-parent-invalid-not-first-owner" (toJson (([0] : List Nat).map (fun x => (meterTagged T [0] [0] c x).value))) (Json.mkObj [("taggedCap",toJson (taggedCap T [0] [0] c))])

#eval do
  let T : Tree := (.node (.leaf 0) (.leaf 1))
  let c : Colors := (⟨(.single []),.keep,.keep⟩ : Colors)
  reviewEmit "missing-parent-invalid-not-default-residue" (toJson (([1] : List Nat).map (fun x => (meterTagged T [0] [] c x).value))) (Json.mkObj [("taggedCap",toJson (taggedCap T [0] [] c))])

#eval do
  let T : Tree := (.node (.leaf 0) (.leaf 1))
  let c : Colors := (⟨(.single []),.keep,.keep⟩ : Colors)
  reviewEmit "missing-target-label-lookup-refusal" (toJson (([99] : List Nat).map (fun x => (meterTagged T [99] [] c x).value))) (Json.mkObj [("taggedCap",toJson (taggedCap T [99] [] c))])

#eval do
  let T : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))
  let c : Colors := (⟨(.single [false,false,false]),.keep,.keep⟩ : Colors)
  reviewEmit "nonvertex-target-not-silently-original-region" (toJson (([0] : List Nat).map (fun x => (meterTagged T [0,2] [1] c x).value))) (Json.mkObj [("taggedCap",toJson (taggedCap T [0,2] [1] c))])

#eval do
  reviewEmit "original-address-not-suppressed-path" (toJson (([1,2] : List Nat).map (fun x => ja ((meterLeafList [x] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))).value.headD [])))) (Json.mkObj [])

#eval do
  reviewEmit "empty-leaf-hull" (toJson ((meterMinimal [] (.node (.leaf 0) (.leaf 1))).value.map ja)) (Json.mkObj [])

#eval do
  reviewEmit "singleton-root-hull" (toJson ((meterMinimal [7] (.leaf 7)).value.map ja)) (Json.mkObj [])

#eval do
  reviewEmit "singleton-leaf-hull-excludes-input-root" (toJson ((meterMinimal [0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))).value.map ja)) (Json.mkObj [])

#eval do
  reviewEmit "two-leaf-original-minimal-hull" (toJson ((meterMinimal [0,1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))).value.map ja)) (Json.mkObj [])

#eval do
  reviewEmit "empty-joint-color-set" (toJson ((meterJointColors [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [false] [true]).value.map (fun p => [p.1,p.2]))) (Json.mkObj [("work",toJson ((meterJointColors [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [false] [true]).work))])

#eval do
  reviewEmit "leafless-middle-not-third-joint-region" (toJson ((meterJointColors [0,3] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [false] [true]).value.map (fun p => [p.1,p.2]))) (Json.mkObj [("work",toJson ((meterJointColors [0,3] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [false] [true]).work))])

#eval do
  reviewEmit "four-joint-signatures-counted" (toJson ((meterJointColors [0,1,2,3] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [false] [true]).value.map (fun p => [p.1,p.2]))) (Json.mkObj [("work",toJson ((meterJointColors [0,1,2,3] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [false] [true]).work))])

#eval do
  let r := meterCliqueSelection (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.node (.node (.leaf 3) (.leaf 4)) (.leaf 5))) [0,3] [1,4] [2,5]
  reviewEmit "actual-clique-original-overlap-selector" (toJson (r.value.map ja)) (Json.mkObj [("work",toJson (r.work))])

#eval do
  let v : RMAF.Vertex := [false]
  let w : RMAF.Vertex := [true]
  let cs := cliqueColors v
  reviewEmit "literal-clique-alternative-identities" (toJson [jdesc v w cs.1,jdesc v w cs.2.1,jdesc v w cs.2.2]) (Json.mkObj [])

#eval do
  let v : RMAF.Vertex := [false]
  let w : RMAF.Vertex := [true]
  let cs := chainColors v w
  reviewEmit "literal-chain-alternative-identities" (toJson [jdesc v w cs.1,jdesc v w cs.2.1,jdesc v w cs.2.2.1,jdesc v w cs.2.2.2]) (Json.mkObj [])

#eval do
  let v : RMAF.Vertex := [false]
  let w : RMAF.Vertex := [true]
  let cs := chainColors v w
  reviewEmit "literal-joint-alternative-identities" (toJson [jdesc v w cs.2.1,jdesc v w cs.2.2.1]) (Json.mkObj [])

#eval do
  let lists : List Owned := [(⟨[(⟨[[0]],[]⟩ : Output)],0,0,0,0⟩ : Owned),(⟨[(⟨[[1]],[]⟩ : Output)],0,0,0,0⟩ : Owned),(⟨[(⟨[[0]],[]⟩ : Output)],0,0,0,0⟩ : Owned)]
  let r := lists.foldl (fun a r => appendOwned a r) ownedEmpty
  reviewEmit "outer-left-raw-duplicates-retained" (toJson (r.outputs.map (fun o => (o.partition.headD []).headD 0))) (Json.mkObj [("copied",toJson (r.copied)),("work",toJson (r.work))])

#eval do
  let lists : List Owned := [(⟨[(⟨[[0]],[]⟩ : Output)],0,0,0,0⟩ : Owned),(⟨[(⟨[[1]],[]⟩ : Output)],0,0,0,0⟩ : Owned),(⟨[(⟨[[2]],[]⟩ : Output)],0,0,0,0⟩ : Owned),(⟨[(⟨[[3]],[]⟩ : Output)],0,0,0,0⟩ : Owned)]
  let r := lists.foldr appendOwned ownedEmpty
  reviewEmit "outer-right-four-singletons" (toJson (r.outputs.map (fun o => (o.partition.headD []).headD 0))) (Json.mkObj [("copied",toJson (r.copied)),("work",toJson (r.work))])

#eval do
  let lists : List Owned := [(⟨[],0,0,0,0⟩ : Owned),(⟨[],0,0,0,0⟩ : Owned)]
  let r := lists.foldl (fun a r => appendOwned a r) ownedEmpty
  reviewEmit "outer-empty-left-still-has-base-call" (toJson (r.outputs.map (fun o => (o.partition.headD []).headD 0))) (Json.mkObj [("copied",toJson (r.copied)),("work",toJson (r.work))])

#eval do
  let lists : List Owned := [(⟨[],0,0,0,0⟩ : Owned),(⟨[],0,0,0,0⟩ : Owned),(⟨[],0,0,0,0⟩ : Owned)]
  let r := lists.foldl (fun a r => appendOwned a r) ownedEmpty
  reviewEmit "outer-refusal-left-cells-not-free" (toJson (r.outputs.map (fun o => (o.partition.headD []).headD 0))) (Json.mkObj [("copied",toJson (r.copied)),("work",toJson (r.work))])

#eval do
  let lists : List Owned := [(⟨[(⟨[[0]],[]⟩ : Output)],0,0,0,0⟩ : Owned),(⟨[(⟨[[1]],[]⟩ : Output)],0,0,0,0⟩ : Owned)]
  let r := lists.foldl (fun a r => appendOwned a r) ownedEmpty
  reviewEmit "literal-dedup-does-not-hide-partition-order" (toJson (r.outputs.map (fun o => (o.partition.headD []).headD 0))) (Json.mkObj [("copied",toJson (r.copied)),("work",toJson (r.work))])

#eval do
  let one := meterWhole (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)) [0,1] [] (⟨(.single []),.keep,.keep⟩ : Colors) 1
  let rs : List Owned := List.replicate 3 one
  let r := rs.foldl (fun a x => appendOwned a x) ownedEmpty
  reviewEmit "whole-clique-unchanged-budget-calls" (Json.mkObj [("outputs",toJson (r.outputs.map jo)),("colorCalls",toJson r.colorCalls),("pruned",toJson r.pruned)]) (Json.mkObj [("copied",toJson (r.copied)),("work",toJson (r.work))])

#eval do
  let one := meterWhole (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)) [0,1] [] (⟨(.single []),.keep,.keep⟩ : Colors) 1
  let rs : List Owned := List.replicate 4 one
  let r := rs.foldl (fun a x => appendOwned a x) ownedEmpty
  reviewEmit "whole-chain-unchanged-budget-calls" (Json.mkObj [("outputs",toJson (r.outputs.map jo)),("colorCalls",toJson r.colorCalls),("pruned",toJson r.pruned)]) (Json.mkObj [("copied",toJson (r.copied)),("work",toJson (r.work))])

#eval do
  let one := meterWhole (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)) [0,1] [] (⟨(.single []),.keep,.keep⟩ : Colors) 1
  let rs : List Owned := List.replicate 2 one
  let r := rs.foldl (fun a x => appendOwned a x) ownedEmpty
  reviewEmit "whole-joint-unchanged-budget-calls" (Json.mkObj [("outputs",toJson (r.outputs.map jo)),("colorCalls",toJson r.colorCalls),("pruned",toJson r.pruned)]) (Json.mkObj [("copied",toJson (r.copied)),("work",toJson (r.work))])

#eval do
  let one := meterWhole (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)) [0,1] [] (⟨(.single []),.keep,.keep⟩ : Colors) 0
  let rs : List Owned := List.replicate 3 one
  let r := rs.foldl (fun a x => appendOwned a x) ownedEmpty
  reviewEmit "whole-zero-budget-keeps-callback-and-local-work" (Json.mkObj [("outputs",toJson (r.outputs.map jo)),("colorCalls",toJson r.colorCalls),("pruned",toJson r.pruned)]) (Json.mkObj [("copied",toJson (r.copied)),("work",toJson (r.work))])

#eval do
  let one := meterWhole (.node (.leaf 7) (.leaf 7)) (.node (.leaf 7) (.leaf 8)) [7] [8] (⟨(.single []),.keep,.keep⟩ : Colors) 3
  let rs : List Owned := List.replicate 3 one
  let r := rs.foldl (fun a x => appendOwned a x) ownedEmpty
  reviewEmit "duplicate-source-refusal-zero-callbacks" (Json.mkObj [("outputs",toJson (r.outputs.map jo)),("colorCalls",toJson r.colorCalls),("pruned",toJson r.pruned)]) (Json.mkObj [("copied",toJson (r.copied)),("work",toJson (r.work))])

#eval do
  let one := meterWhole (.node (.leaf 0) (.leaf 340282366920938463463374607431768211456)) (.node (.leaf 0) (.leaf 340282366920938463463374607431768211456)) [0,340282366920938463463374607431768211456] [] (⟨(.single []),.keep,.keep⟩ : Colors) 340282366920938463463374607431768211456
  let rs : List Owned := List.replicate 2 one
  let r := rs.foldl (fun a x => appendOwned a x) ownedEmpty
  reviewEmit "oversized-budget-and-label-encoding-not-erased" (Json.mkObj [("outputs",toJson (r.outputs.map jo)),("colorCalls",toJson r.colorCalls),("pruned",toJson r.pruned)]) (Json.mkObj [("copied",toJson (r.copied)),("work",toJson (r.work))])

#eval do
  let lists : List Owned := [(⟨[(⟨[[0]],[]⟩ : Output),(⟨[[1]],[]⟩ : Output),(⟨[[2]],[]⟩ : Output),(⟨[[3]],[]⟩ : Output),(⟨[[4]],[]⟩ : Output),(⟨[[5]],[]⟩ : Output),(⟨[[6]],[]⟩ : Output),(⟨[[7]],[]⟩ : Output),(⟨[[8]],[]⟩ : Output),(⟨[[9]],[]⟩ : Output),(⟨[[10]],[]⟩ : Output),(⟨[[11]],[]⟩ : Output),(⟨[[12]],[]⟩ : Output),(⟨[[13]],[]⟩ : Output),(⟨[[14]],[]⟩ : Output),(⟨[[15]],[]⟩ : Output)],0,0,0,0⟩ : Owned),(⟨[(⟨[[16]],[]⟩ : Output)],0,0,0,0⟩ : Owned)]
  let r := lists.foldl (fun a r => appendOwned a r) ownedEmpty
  reviewEmit "outer-long-left-list-not-unit-work" (toJson (r.outputs.map (fun o => (o.partition.headD []).headD 0))) (Json.mkObj [("copied",toJson (r.copied)),("work",toJson (r.work))])

#eval do
  let r := meterClique (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)) [0,1] [] [] 0
  reviewEmit "actual-clique-q0" (Json.mkObj [("outputs",toJson (r.outputs.map jo)),("colorCalls",toJson r.colorCalls),("pruned",toJson r.pruned)]) (Json.mkObj [("copied",toJson r.copied),("work",toJson r.work)])

#eval do
  let r := meterClique (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)) [0,1] [] [] 1
  reviewEmit "actual-clique-q1" (Json.mkObj [("outputs",toJson (r.outputs.map jo)),("colorCalls",toJson r.colorCalls),("pruned",toJson r.pruned)]) (Json.mkObj [("copied",toJson r.copied),("work",toJson r.work)])

#eval do
  let r := meterChain (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)) [0,1] [] [] [] 0
  reviewEmit "actual-chain-q0" (Json.mkObj [("outputs",toJson (r.outputs.map jo)),("colorCalls",toJson r.colorCalls),("pruned",toJson r.pruned)]) (Json.mkObj [("copied",toJson r.copied),("work",toJson r.work)])

#eval do
  let r := meterChain (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)) [0,1] [] [] [] 1
  reviewEmit "actual-chain-q1" (Json.mkObj [("outputs",toJson (r.outputs.map jo)),("colorCalls",toJson r.colorCalls),("pruned",toJson r.pruned)]) (Json.mkObj [("copied",toJson r.copied),("work",toJson r.work)])

#eval do
  let r := meterDiagonal (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)) [0,1] [] [] [] 0
  reviewEmit "actual-joint-q0" (Json.mkObj [("outputs",toJson (r.outputs.map jo)),("colorCalls",toJson r.colorCalls),("pruned",toJson r.pruned)]) (Json.mkObj [("copied",toJson r.copied),("work",toJson r.work)])

#eval do
  let r := meterDiagonal (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)) [0,1] [] [] [] 1
  reviewEmit "actual-joint-q1" (Json.mkObj [("outputs",toJson (r.outputs.map jo)),("colorCalls",toJson r.colorCalls),("pruned",toJson r.pruned)]) (Json.mkObj [("copied",toJson r.copied),("work",toJson r.work)])

#eval reviewEmit "local-max3" (toJson (colorLabel (.leaf 0) [] 0)) (Json.mkObj [])

#eval reviewEmit "joint-max15" (toJson (jointLabel (.leaf 0) [] [] 0)) (Json.mkObj [])

#eval reviewEmit "tagged-max47" (toJson (colors (.leaf 0) [] [] ⟨.keep,.keep,.joint [] []⟩ 0)) (Json.mkObj [])
