import BoundedRequests
namespace Universal233.Rule5PaidOrdinary
open RMAF ForestState ForestMinCompletion
open Rule5Case322 Rule5FinalClassification Case322PaidGuard Rule5PaidSelector

def bestFor (actual : Ordinary) {T S : Tree} (R : SelectedPaid T S) (q : Nat) : Option Forest :=
 best List.length (originalAccepted T S q) (answers actual R q)

inductive SelectedResult where
 | builderRefused
 | answered (answer : Option Forest)
 deriving DecidableEq, Repr

/-- Every affordable original request occurrence is evaluated, flattened and
checked as an original q-feasible forest before minimum-length selection. -/
def solveSelected (actual : Ordinary) (T S : Tree) (a b q : Nat) : SelectedResult :=
 match buildSelected T S a b with
 | none => .builderRefused
 | some R => .answered (bestFor actual R q)

theorem bestFor_sound (actual : Ordinary) {T S : Tree} (R : SelectedPaid T S) (q : Nat)
 {F : Forest} (h : bestFor actual R q=some F) : agreement T S F=true ∧ F.length-1≤q := by
 have hs := (best_spec List.length (originalAccepted T S q) (answers actual R q) F h).2.1
 simpa [originalAccepted] using hs

theorem bestFor_complete (actual : Ordinary) {T S : Tree} {a b : Nat}
 {R : SelectedPaid T S} (built : buildSelected T S a b=some R) (q : Nat)
 (below : BelowIH q actual) (G : Forest) (ha : agreement T S G=true) (budget : G.length-1≤q) :
 ∃ F,bestFor actual R q=some F ∧ F.length≤G.length := by
 obtain ⟨H,hH,accepted,len⟩ := answers_cover actual built q below G ha budget
 obtain ⟨F,hF⟩ := best_exists List.length (originalAccepted T S q) (answers actual R q) H hH accepted
 have least := (best_spec List.length (originalAccepted T S q) (answers actual R q) F hF).2.2 H hH accepted
 exact ⟨F,hF,Nat.le_trans least len⟩

theorem bestFor_minimum (actual : Ordinary) {T S : Tree} {a b : Nat}
 {R : SelectedPaid T S} (built : buildSelected T S a b=some R) (q : Nat)
 (below : BelowIH q actual) {F : Forest} (h : bestFor actual R q=some F) :
 ∀ G,agreement T S G=true → F.length≤G.length := by
 have valid := bestFor_sound actual R q h
 intro G hG
 by_cases budget : G.length-1≤q
 · obtain ⟨H,hH,len⟩ := bestFor_complete actual built q below G hG budget
   have eq : H=F := Option.some.inj (hH.symm.trans h)
   simpa [eq] using len
 · omega

theorem solveSelected_sound (actual : Ordinary) (T S : Tree) (a b q : Nat)
 {F : Forest} (h : solveSelected actual T S a b q=.answered (some F)) :
 agreement T S F=true ∧ F.length-1≤q := by
 unfold solveSelected at h
 cases built : buildSelected T S a b with
 | none => simp [built] at h
 | some R =>
   have hb : bestFor actual R q=some F := by simpa [built] using h
   exact bestFor_sound actual R q hb

theorem solveSelected_minimum (actual : Ordinary) (T S : Tree) (a b q : Nat)
 (below : BelowIH q actual) {F : Forest}
 (h : solveSelected actual T S a b q=.answered (some F)) :
 ∀ G,agreement T S G=true → F.length≤G.length := by
 unfold solveSelected at h
 cases built : buildSelected T S a b with
 | none => simp [built] at h
 | some R =>
   have hb : bestFor actual R q=some F := by simpa [built] using h
   exact bestFor_minimum actual built q below hb

theorem solveSelected_complete (actual : Ordinary) {T S : Tree} {i u v : RMAF.Vertex}
 {a b : Nat} {d : BadSelection} (ch : CoreGraph.CherryAt T i a b)
 (ad : Rule5Local.admitted T S a b=true)
 (selected : selectFinal T S a b=some (.remaining d (.second u v))) (q : Nat)
 (below : BelowIH q actual) (G : Forest) (ha : agreement T S G=true) (budget : G.length-1≤q) :
 ∃ F,solveSelected actual T S a b q=.answered (some F) ∧ F.length≤G.length := by
 obtain ⟨R,built,_,_,_⟩ := buildSelected_complete ch ad selected
 obtain ⟨F,hF,len⟩ := bestFor_complete actual built q below G ha budget
 exact ⟨F,by simp [solveSelected,built,hF],len⟩

theorem solveSelected_builder_refused_iff (actual : Ordinary) (T S : Tree) (a b q : Nat) :
 solveSelected actual T S a b q=.builderRefused ↔ buildSelected T S a b=none := by
 cases h : buildSelected T S a b <;> simp [solveSelected,h]

theorem actual_second_never_builder_refuses (actual : Ordinary) {T S : Tree} {i u v : RMAF.Vertex}
 {a b : Nat} {d : BadSelection} (ch : CoreGraph.CherryAt T i a b)
 (ad : Rule5Local.admitted T S a b=true)
 (selected : selectFinal T S a b=some (.remaining d (.second u v))) (q : Nat) :
 solveSelected actual T S a b q≠.builderRefused := by
 obtain ⟨R,built,_,_,_⟩ := buildSelected_complete ch ad selected
 simp [solveSelected,built]

theorem actual_second_feasible_iff (actual : Ordinary) {T S : Tree} {i u v : RMAF.Vertex}
 {a b : Nat} {d : BadSelection} (ch : CoreGraph.CherryAt T i a b)
 (ad : Rule5Local.admitted T S a b=true)
 (selected : selectFinal T S a b=some (.remaining d (.second u v))) (q : Nat)
 (below : BelowIH q actual) :
 (∃ F,solveSelected actual T S a b q=.answered (some F)) ↔
 ∃ G,agreement T S G=true ∧ G.length-1≤q := by
 constructor
 · rintro ⟨F,hF⟩
   exact ⟨F,solveSelected_sound actual T S a b q hF⟩
 · rintro ⟨G,hG,budget⟩
   obtain ⟨F,hF,_⟩ := solveSelected_complete actual ch ad selected q below G hG budget
   exact ⟨F,hF⟩

/-- Original operational role transport keeps every original cut and payment. -/
theorem request_role_payment (T S : Tree) (c : Branch) :
 (Case322Extraction.swapBranch c).originalCuts=c.originalCuts ∧
 paid (Case322Extraction.swapBranch c)=paid c ∧
 Case322Extraction.sourceForest_swap T S c = Case322Extraction.sourceForest_swap T S c := by
 exact ⟨rfl,rfl,rfl⟩
end Universal233.Rule5PaidOrdinary
