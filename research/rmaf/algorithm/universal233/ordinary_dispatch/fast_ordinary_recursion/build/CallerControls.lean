import CallerDefs
namespace OrdinaryCommonSplit.Caller.Controls
open RMAF OrdinaryCommonSplit.Controls
def FM : List (List Nat) := [[6,0,1],[2]]
def FN : List (List Nat) := [[7,3,4],[5]]
def FMrev : List (List Nat) := [[2],[1,6,0]]
def FNrev : List (List Nat) := [[5],[4,7,3]]
theorem actual_marked_replies : agreement markedXT markedXS FM=true ∧
    agreement markedYT markedYS FN=true ∧ agreement markedXT markedXS FMrev=true ∧
    agreement markedYT markedYS FNrev=true := by decide
theorem literal_generated_good : [[0,1,3,4],[2],[5]]∈mergeCandidates X Y 0 3 6 7 FM FN := by decide
theorem actual_checked_merge : replyCost (pickMerge T S X Y 0 3 6 7 FM FN)=some 2 ∧
    (pickMerge T S X Y 0 3 6 7 FM FN).all (fun G=>agreement T S G)=true := by decide
theorem noncanonical_actual_checked_merge : replyCost (pickMerge T S X Y 0 3 6 7 FMrev FNrev)=some 2 ∧
    (pickMerge T S X Y 0 3 6 7 FMrev FNrev).all (fun G=>agreement T S G)=true := by decide
theorem failed_guesses_are_present : (mergeCandidates X Y 0 3 6 7 FMrev FNrev).any
    (fun G=> !(agreement T S G))=true := by decide
end OrdinaryCommonSplit.Caller.Controls
