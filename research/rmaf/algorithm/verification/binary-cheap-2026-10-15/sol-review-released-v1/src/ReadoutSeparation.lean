import IndependentReadout
open Lean Universal233 RMAF CoreProgram Universal233.BinaryCheap Universal233.RankDichotomy
open SourceCoverage VertexGeometry BinaryExchange PairAssembly RankConsumer
namespace IndependentSeparation
def ps : Tree := (.node ((.node ((.node (.leaf 1) (.leaf 2))) ((.node ((.node (.leaf 3) (.leaf 5))) ((.node (.leaf 4) (.leaf 6))))))) (.leaf 7))
def pt : Tree := (.node ((.node ((.node (.leaf 1) ((.node (.leaf 3) (.leaf 4))))) ((.node (.leaf 2) ((.node (.leaf 5) (.leaf 6))))))) (.leaf 7))
def s : Tree := (.node ((.node ((.node ((.node (.leaf 1) (.leaf 2))) (.leaf 3))) ((.node ((.node ((.node (.leaf 5) (.leaf 7))) (.leaf 9))) ((.node ((.node (.leaf 6) (.leaf 8))) (.leaf 10))))))) ((.node (.leaf 11) (.leaf 12))))
def t : Tree := (.node ((.node ((.node (.leaf 1) ((.node ((.node (.leaf 5) (.leaf 6))) ((.node (.leaf 7) (.leaf 8))))))) ((.node ((.node (.leaf 2) (.leaf 3))) ((.node (.leaf 9) (.leaf 10))))))) ((.node (.leaf 11) (.leaf 12))))
def F0 : List (List Nat) := [[1],[2],[3,5],[4],[6],[7]]
def Fprime : List (List Nat) := [[1,2],[3],[5],[4],[6],[7]]
def A : List Nat := [1,2,3]
def B : List Nat := [5,6,7,8,9,10]
def C : List Nat := [11,12]
def D := PairGeometry.descendants t [false,false]
def out := (generate s (cheapColor A B D) 3).outputs
def pubout := (generate ps (cheapColor [3,4,5,6] [1,2] (PairGeometry.descendants pt [false,false])) 6).outputs
#eval IndependentReadout.emit (Json.mkObj [
 ("id",toJson "frozen-separation-controls"),
 ("F_agreement",toJson (agreement ps pt F0)),("Fprime_agreement",toJson (agreement ps pt Fprime)),
 ("F_refines_P",toJson (IndependentReadout.refined F0 [[1,2],[3,4,5,6],[7]])),
 ("F_refines_some_literal_Q",toJson (pubout.any (fun o => IndependentReadout.refined F0 o.partition))),
 ("Fprime_refines_some_literal_Q",toJson (pubout.any (fun o => IndependentReadout.refined Fprime o.partition))),
 ("Fprime_no_larger",toJson (decide (Fprime.length ≤ F0.length))),
 ("local_cost2_agreement",toJson (agreement (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)) (.node (.leaf 1) (.node (.leaf 2) (.leaf 3))) [[1],[2],[3]])),
 ("whole_source_same_address_partition",toJson (DepthOne.forest s (some [false]))),
 ("three_color_rank",toJson (inputRank s (fun x => if C.contains x then 0 else cheapColor A B D x))),
 ("three_color_receipt",IndependentReadout.receiptJson (generate s (fun x => if C.contains x then 0 else cheapColor A B D x) 3)),
 ("one_mass",IndependentReadout.rational (rawQMass 2 out)),
 ("two_identical_occurrences_mass",IndependentReadout.rational (rawQMass 2 (out++out))),
 ("two_identical_raw_occurrences",toJson ((out++out).map IndependentReadout.outputJson))])
end IndependentSeparation
