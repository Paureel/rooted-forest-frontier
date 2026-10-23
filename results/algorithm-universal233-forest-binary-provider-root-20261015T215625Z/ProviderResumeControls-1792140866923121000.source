import PersistentEntry
import ProviderPrecontrols
namespace GenericForest.BinaryProvider.ResumeControls
open GenericForest.ScalarBits GenericForest.BinaryProvider.Controls

def C3 : Capacity:=[(),(),()]
def one : Bits:=[true]
def two : Bits:=[false,true]
def three : Bits:=[true,true]
def T : Tree:=.node (.leaf one) (.node (.leaf two) (.leaf three))
def pair : Tree:=.node (.leaf one) (.leaf two)

theorem counter_exact : decode (countLabel C3 a [a,paddedA,[false]]).value=2 ∧
 (countLabel C3 a [a,paddedA,[false]]).value.length=3 ∧
 (countLabel C3 a [a,paddedA,[false]]).work=386 := by decide +kernel

theorem partition_exact : (partitionLabels C3 [a] [[paddedA]]).value=true ∧
 (partitionLabels C3 [a] [[paddedA]]).work=378 ∧
 (partitionFromInput [a] [[paddedA]]).value=true := by decide +kernel

theorem partition_nulls : (partitionFromInput [] []).value=true ∧
 (partitionFromInput [a] []).value=false ∧ (partitionFromInput [a] [[]]).value=false ∧
 (partitionFromInput [a] [[a],[paddedA]]).value=false ∧
 (partitionFromInput [a] [[[false]]]).value=false := by decide +kernel

theorem restriction_exact : (restrictLabels [one,three] T).value=some (.node (.leaf one) (.leaf three)) ∧
 (restrictionAgreesLabels T (.node (.leaf three) (.leaf one)) [one,three]).value=true := by decide +kernel

theorem original_unary_addresses : (minimalLabels [two,three] T).value=[[true],[true,false],[true,true]] ∧
 (rootedLabels [two] T).value=[[],[true],[true,false]] := by decide +kernel

theorem checker_known : (checkerFromInput (some (.leaf a)) [.leaf paddedA] [] [[a]]).value=some [[a]] ∧
 (checkerFromInput none [] [] []).value=some [] ∧
 (checkerFromInput (some (.leaf a)) [.leaf paddedA] [] [[a],[paddedA]]).value=none := by decide +kernel

theorem checker_budget : (checkerFromInput (some pair) [pair] [] [[one],[two]]).value=none ∧
 (checkerFromInput (some pair) [pair] one [[one],[two]]).value=some [[one],[two]] := by decide +kernel

theorem setup_paid : 0<(checkerCapacity (some pair) [pair] one [[one],[two]]).work ∧
 (checkerCapacity (some pair) [pair] one [[one],[two]]).work<
 (checkerFromInput (some pair) [pair] one [[one],[two]]).work := by decide +kernel
end GenericForest.BinaryProvider.ResumeControls
