import RMAF
import CoreProgram
namespace Universal233.ScaffoldWitness
open RMAF
def originalT : Tree := (.node (.node (.leaf 6) (.node (.node (.node (.leaf 0) (.leaf 2)) (.leaf 4)) (.node (.node (.leaf 1) (.node (.node (.node (.node (.node (.leaf 12) (.leaf 13)) (.leaf 11)) (.leaf 10)) (.leaf 9)) (.leaf 3))) (.leaf 5)))) (.node (.leaf 7) (.leaf 8)))
def originalS : Tree := (.node (.leaf 6) (.node (.node (.leaf 7) (.node (.node (.node (.leaf 2) (.node (.node (.node (.node (.node (.leaf 9) (.leaf 11)) (.leaf 12)) (.leaf 10)) (.leaf 13)) (.leaf 3))) (.leaf 1)) (.leaf 0))) (.node (.leaf 8) (.node (.leaf 4) (.leaf 5)))))
def sourceParents : List (List Nat) := [[0, 1, 2, 3, 9, 10, 11, 12, 13], [4, 5], [6, 7, 8]]
def paidPartitions : List (List (List Nat)) := [[[0], [1, 3, 9, 10, 11, 12, 13], [2], [4, 5], [6, 7, 8]], [[0, 2], [1], [3, 9, 10, 11, 12, 13], [4, 5], [6, 7, 8]], [[0, 1, 2, 3, 9, 10, 11, 12, 13], [4], [5], [6, 7, 8]]]
def localT : Tree := (.node (.node (.node (.node (.node (.leaf 4) (.leaf 5)) (.leaf 3)) (.leaf 2)) (.leaf 1)) (.leaf 0))
def localS : Tree := (.node (.node (.node (.node (.node (.leaf 1) (.leaf 3)) (.leaf 4)) (.leaf 2)) (.leaf 5)) (.leaf 0))
def localWitness : List (List Nat) := [[0, 2, 3, 4], [1], [5]]
theorem properOriginalT : (leaves originalT).Nodup := by decide
theorem properOriginalS : (leaves originalS).Nodup := by decide
theorem sourceParentsPartition : partitionCheck (leaves originalS) sourceParents = true := by decide
theorem sourceParentsDisjoint : pairwiseEmbeddings originalS sourceParents = true := by decide
theorem paidSourceValid : paidPartitions.all (agreement originalS originalS) = true := by decide
theorem paidTargetDisjoint : paidPartitions.all (pairwiseEmbeddings originalT) = true := by decide
theorem exactlyOneBadParent : paidPartitions.all (fun bs => (bs.filter (fun b => !restrictionAgrees originalT originalS b)).length == 1) = true := by decide
theorem localTwoCutsSuffice : agreement localT localS localWitness = true := by decide
theorem localOneCutImpossible : (assignments 6 2).all (fun a => !(agreement localT localS (blocks a))) = true := by decide
theorem oldMassFails : 233^4 < 2 * 233^3 * 100 + 233 * 100^3 + 2 * 100^4 := by decide
def sourceA : Tree := (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 2) (.node (.leaf 3) (.node (.node (.node (.node (.leaf 9) (.leaf 11)) (.leaf 12)) (.leaf 10)) (.leaf 13))))))
def prototypeAPartitions : List (List (List Nat)) := [[[0], [1, 3, 9, 10, 11, 12, 13], [2]], [[0, 2], [1], [3, 9, 10, 11, 12, 13]]]
def prototypeACuts : List (List Vertex) := [[[true, true, false], [false]], [[true, true, true], [true, false]]]
def aColor (x : Nat) : Nat := if x = 0 ∨ x = 2 then 0 else 1
def actualA := Universal233.CoreProgram.generate sourceA aColor 2
def sameMembers {α : Type} [BEq α] (a b : List α) : Bool := a.all b.contains && b.all a.contains
def samePartition (a b : List (List Nat)) : Bool := a.all (fun x => b.any (sameMembers x)) && b.all (fun x => a.any (sameMembers x))
theorem productionACharges : actualA.outputs.map (fun o => o.sourceCuts.length) = [2,2] := by decide
theorem productionAValidPayload : actualA.outputs.all (fun o => partitionCheck (leaves sourceA) o.partition) = true := by decide
theorem productionAPartitions : (actualA.outputs.all (fun o => prototypeAPartitions.any (samePartition o.partition)) && prototypeAPartitions.all (fun p => actualA.outputs.any (fun o => samePartition o.partition p))) = true := by decide
theorem productionACuts : (actualA.outputs.all (fun o => prototypeACuts.any (sameMembers o.sourceCuts)) && prototypeACuts.all (fun p => actualA.outputs.any (fun o => sameMembers o.sourceCuts p))) = true := by decide
theorem productionColorSwap : (Universal233.CoreProgram.generate sourceA (fun x => 1 - aColor x) 2).outputs = actualA.outputs := by decide
theorem productionBCharge : (Universal233.CoreProgram.generate (.node (.leaf 4) (.leaf 5)) (fun x => x) 1).outputs.map (fun o => o.sourceCuts.length) = [1] := by decide
#print axioms productionACharges
#print axioms productionAValidPayload
#print axioms productionAPartitions
#print axioms productionACuts
#print axioms productionColorSwap
#print axioms productionBCharge
#print axioms properOriginalT
#print axioms properOriginalS
#print axioms sourceParentsPartition
#print axioms sourceParentsDisjoint
#print axioms paidSourceValid
#print axioms paidTargetDisjoint
#print axioms exactlyOneBadParent
#print axioms localTwoCutsSuffice
#print axioms localOneCutImpossible
#print axioms oldMassFails
end Universal233.ScaffoldWitness
