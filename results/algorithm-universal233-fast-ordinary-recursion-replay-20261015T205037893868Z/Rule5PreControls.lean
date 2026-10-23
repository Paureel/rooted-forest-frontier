import Rule5Defs
namespace Universal233.Rule5Local.Pre
open RMAF HardParent CherryBranching
set_option maxRecDepth 8000
def sixT : Tree := .node (.node (.node (.node (.leaf 14) (.node (.leaf 0) (.leaf 1))) (.leaf 15)) (.leaf 2)) (.leaf 16)
def sixS : Tree := .node (.node (.node (.leaf 0) (.node (.leaf 14) (.node (.leaf 15) (.leaf 16)))) (.leaf 2)) (.leaf 1)
theorem six_admitted : admitted sixT sixS 0 1 = true := by decide
theorem six_incident : (incident sixT [14,15,16]).length = 2 := by decide
def thirdT : Tree := .node (.leaf 2) (.node (.leaf 9) (.node (.leaf 14) (.node (.leaf 10) (.node (.leaf 13) (.node (.leaf 0) (.leaf 1))))))
def thirdS : Tree := .node (.node (.node (.leaf 0) (.node (.leaf 13) (.node (.leaf 14) (.node (.leaf 9) (.leaf 10))))) (.leaf 2)) (.leaf 1)
theorem third_admitted : admitted thirdT thirdS 0 1 = true := by decide
theorem third_incident : (incident thirdT [13,14,9,10]).length = 2 := by decide
def firstT : Tree := .node (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 9) (.node (.leaf 14) (.node (.leaf 10) (.node (.leaf 13) (.leaf 2)))))) (.leaf 12)
def firstS : Tree := .node (.node (.node (.node (.leaf 0) (.node (.leaf 13) (.node (.leaf 14) (.node (.leaf 9) (.leaf 10))))) (.leaf 2)) (.leaf 1)) (.leaf 12)
theorem first_admitted : admitted firstT firstS 0 1 = true := by decide
theorem first_incident : (incident firstT [13,14,9,10]).length = 2 := by decide
def commonT : Tree := .node (.node (.node (.node (.node (.leaf 6) (.node (.leaf 3) (.leaf 4))) (.leaf 7)) (.leaf 5)) (.leaf 8)) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
def commonS : Tree := .node (.node (.node (.leaf 0) (.node (.node (.node (.leaf 3) (.node (.leaf 6) (.node (.leaf 7) (.leaf 8)))) (.leaf 5)) (.leaf 4))) (.leaf 2)) (.leaf 1)
theorem common_admitted : admitted commonT commonS 0 1 = true := by decide
theorem common_incident : (incident commonT [3,6,7,8,5,4]).length = 1 := by decide
theorem common_emits : (commonSplit? commonT commonS 0 1 [3,6,7,8,5,4]).isSome = true := by decide
def twoT : Tree := .node (.node (.leaf 9) (.node (.node (.node (.node (.leaf 6) (.node (.leaf 3) (.leaf 4))) (.leaf 7)) (.leaf 5)) (.leaf 8))) (.node (.leaf 10) (.node (.leaf 0) (.leaf 1)))
def twoS : Tree := .node (.node (.leaf 0) (.node (.leaf 9) (.leaf 10))) (.node (.leaf 1) (.node (.node (.node (.leaf 3) (.node (.leaf 6) (.node (.leaf 7) (.leaf 8)))) (.leaf 5)) (.leaf 4)))
theorem two_admitted : admitted twoT twoS 0 1 = true := by decide
def largeT : Tree := .node (.leaf 11) (.node (.node (.leaf 9) (.node (.node (.node (.node (.leaf 6) (.node (.leaf 3) (.leaf 4))) (.leaf 7)) (.leaf 5)) (.leaf 8))) (.node (.leaf 10) (.node (.leaf 0) (.leaf 1))))
def largeS : Tree := .node (.node (.leaf 0) (.node (.leaf 11) (.node (.leaf 9) (.leaf 10)))) (.node (.leaf 1) (.node (.node (.node (.leaf 3) (.node (.leaf 6) (.node (.leaf 7) (.leaf 8)))) (.leaf 5)) (.leaf 4)))
theorem large_admitted : admitted largeT largeS 0 1 = true := by decide
def outsideT : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 10) (.node (.leaf 2) (.node (.leaf 9) (.node (.node (.node (.node (.leaf 6) (.node (.leaf 3) (.leaf 4))) (.leaf 7)) (.leaf 5)) (.leaf 8)))))
def outsideS : Tree := .node (.node (.node (.node (.leaf 0) (.node (.node (.node (.leaf 3) (.node (.leaf 6) (.node (.leaf 7) (.leaf 8)))) (.leaf 5)) (.leaf 4))) (.leaf 2)) (.leaf 1)) (.node (.leaf 9) (.leaf 10))
theorem outside_admitted : admitted outsideT outsideS 0 1 = true := by decide
def strictF : List (List Nat) := [[0,2],[1],[13],[14],[9],[10],[12]]
def exchangeG : List (List Nat) := [[0,1],[2],[13],[14],[9],[10],[12]]
theorem strict_valid : agreement firstT firstS strictF = true := by decide
theorem replacement_valid : agreement firstT firstS exchangeG = true := by decide
theorem exchange_no_larger : exchangeG.length = strictF.length := by decide
theorem strict_not_refines : refinesCheck strictF (pendantPartition firstS 0 1) = false := by decide
def missingT : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.node (.node (.leaf 14) (.leaf 15)) (.leaf 16)))
theorem missing_priority_rejected : earlierClear missingT sixS = false := by decide
def clearanceT : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.node (.leaf 15) (.leaf 12)) (.node (.leaf 14) (.node (.leaf 16) (.leaf 2))))
theorem clearance_rejected : pairwiseEmbeddings clearanceT (pendantPartition (.node sixS (.leaf 12)) 0 1) = false := by decide
end Universal233.Rule5Local.Pre
