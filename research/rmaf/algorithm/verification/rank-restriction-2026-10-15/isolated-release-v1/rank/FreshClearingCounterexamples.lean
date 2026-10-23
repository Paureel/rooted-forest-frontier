import Requests
open RMAF Universal233 Universal233.CoreProgram Universal233.Assembly VertexGeometry
namespace FreshClearingCounterexamples

def S_one : Tree := (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 4)) (.node (.node (.leaf 2) (.leaf 3)) (.leaf 5)))
def T_one : Tree := (.node (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.leaf 4) (.leaf 5)))
def o_one : Output := ⟨[[2,3],[0,1],[4,5]],[[true,false],[false,false]]⟩
theorem actual_one_clearing_target_overlap :
    o_one ∈ (generate S_one (localColor T_one (.at [])) 5).outputs ∧
    partitionCheck (leaves S_one) o_one.partition = true ∧
    partitionCheck (leaves T_one) o_one.partition = true ∧
    pairwiseEmbeddings S_one o_one.partition = true ∧
    pairwiseEmbeddings T_one o_one.partition = false ∧
    o_one.partition.all (fun b => [[]].all
      (fun v => !(minimalVertices b T_one).contains v)) = true ∧
    o_one.partition.all (fun U =>
      match restrict U T_one,restrict U S_one with
      | some t,some s => agreement t s [U]
      | _,_ => false) = true ∧
    agreement T_one S_one o_one.partition = false := by decide
#print axioms actual_one_clearing_target_overlap

def S_two : Tree := (.node (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 4)) (.node (.node (.leaf 2) (.leaf 3)) (.leaf 5))) (.leaf 6))
def T_two : Tree := (.node (.node (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.leaf 4) (.leaf 5))) (.leaf 6))
def o_two : Output := ⟨[[2,3],[0,1],[6],[4,5]],[[false,true,false],[false,false,false],[true]]⟩
theorem actual_two_clearing_target_overlap :
    o_two ∈ (generate S_two (localColor T_two (.both [] [false])) 6).outputs ∧
    partitionCheck (leaves S_two) o_two.partition = true ∧
    partitionCheck (leaves T_two) o_two.partition = true ∧
    pairwiseEmbeddings S_two o_two.partition = true ∧
    pairwiseEmbeddings T_two o_two.partition = false ∧
    o_two.partition.all (fun b => [[],[false]].all
      (fun v => !(minimalVertices b T_two).contains v)) = true ∧
    o_two.partition.all (fun U =>
      match restrict U T_two,restrict U S_two with
      | some t,some s => agreement t s [U]
      | _,_ => false) = true ∧
    agreement T_two S_two o_two.partition = false := by decide
#print axioms actual_two_clearing_target_overlap

end FreshClearingCounterexamples
