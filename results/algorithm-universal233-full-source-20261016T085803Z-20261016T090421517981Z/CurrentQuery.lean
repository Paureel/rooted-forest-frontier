import LocalExact
import ForestPretestSemantics
namespace Universal233.Rule5PaidOrdinary
open RMAF ForestState ForestMinCompletion
abbrev Forest := List (List Nat)
abbrev Ordinary := Tree → Tree → Nat → Option Forest

inductive CurrentResult where
 | malformed
 | answered (answer : Option Forest)
 deriving DecidableEq, Repr

/-- Executable current-state query. The only fallback receives the original
actual callback. Noncomputable completion occurs only inside imported proofs. -/
def currentQuery (actual : Ordinary) (T : Option Tree) (ss : List Tree) (r : Nat) : CurrentResult :=
 match ForestPretest01.pretest01 T ss with
 | .refused => .malformed
 | .found F => .answered (if additionalCost ss F≤r then some F else none)
 | .rejected => .answered (if r≤1 then none else GenericForest.solve actual T ss r)

def CurrentResult.answer? : CurrentResult → Option Forest
 | .malformed => none
 | .answered answer => answer

def currentAnswer (actual : Ordinary) (T : Option Tree) (ss : List Tree) (r : Nat) : Option Forest :=
 (currentQuery actual T ss r).answer?

theorem pretest_length_minimum {T : Option Tree} {ss : List Tree} {F : Forest}
 (h : ForestPretest01.pretest01 T ss=.found F) :
 ∀ G,agrees T ss G=true → F.length≤G.length := by
 obtain ⟨ha,_,least⟩ := ForestPretest01.found_globally_minimum T ss F h
 intro G hG
 have hf := ForestGroups.sources_le_blocks T ss F ha
 have hg := ForestGroups.sources_le_blocks T ss G hG
 have hmin := least G hG
 simp only [additionalCost] at hmin
 omega

theorem actual_solve_minimum (actual : Ordinary) (T : Option Tree) (ss : List Tree) (r : Nat)
 (ih : LocalOrdinaryIH r actual) {F : Forest} (answer : GenericForest.solve actual T ss r=some F) :
 ∀ G,agrees T ss G=true → F.length≤G.length := by
 have hs := GenericForest.solve_sound actual T ss r F answer
 intro G hG
 by_cases budget : additionalCost ss G≤r
 · obtain ⟨H,hH,len⟩ := GenericForest.LocalIH.exact_at_current_budget actual r ih T ss G hG budget
   have he : H=F := Option.some.inj (hH.symm.trans answer)
   simpa [he] using len
 · simp only [additionalCost] at hs budget
   omega

theorem currentQuery_sound (actual : Ordinary) (T : Option Tree) (ss : List Tree) (r : Nat)
 {F : Forest} (h : currentQuery actual T ss r=.answered (some F)) :
 agrees T ss F=true ∧ additionalCost ss F≤r := by
 cases hp : ForestPretest01.pretest01 T ss with
 | refused => simp [currentQuery,hp] at h
 | found G =>
   by_cases budget : additionalCost ss G≤r
   · have he : G=F := by simpa [currentQuery,hp,budget] using h
     subst G
     exact ⟨(ForestPretest01.found_globally_minimum T ss F hp).1,budget⟩
   · simp [currentQuery,hp,budget] at h
 | rejected =>
   by_cases small : r≤1
   · simp [currentQuery,hp,small] at h
   · have answer : GenericForest.solve actual T ss r=some F := by simpa [currentQuery,hp,small] using h
     exact GenericForest.solve_sound actual T ss r F answer

theorem currentQuery_minimum (actual : Ordinary) (T : Option Tree) (ss : List Tree) (r : Nat)
 (ih : LocalOrdinaryIH r actual) {F : Forest} (h : currentQuery actual T ss r=.answered (some F)) :
 ∀ G,agrees T ss G=true → F.length≤G.length := by
 cases hp : ForestPretest01.pretest01 T ss with
 | refused => simp [currentQuery,hp] at h
 | found H =>
   by_cases budget : additionalCost ss H≤r
   · have he : H=F := by simpa [currentQuery,hp,budget] using h
     subst H
     exact pretest_length_minimum hp
   · simp [currentQuery,hp,budget] at h
 | rejected =>
   by_cases small : r≤1
   · simp [currentQuery,hp,small] at h
   · have answer : GenericForest.solve actual T ss r=some F := by simpa [currentQuery,hp,small] using h
     exact actual_solve_minimum actual T ss r ih answer

theorem currentQuery_complete (actual : Ordinary) (T : Option Tree) (ss : List Tree) (r : Nat)
 (ih : LocalOrdinaryIH r actual) (G : Forest) (ha : agrees T ss G=true) (budget : additionalCost ss G≤r) :
 ∃ F,currentQuery actual T ss r=.answered (some F) ∧ F.length≤G.length := by
 cases hp : ForestPretest01.pretest01 T ss with
 | refused =>
   have malformed := (ForestPretest01.refused_iff T ss).1 hp
   have proper := (ForestState.agrees_parts T ss G ha).1
   simp [proper] at malformed
 | found F =>
   have hs := ForestPretest01.found_globally_minimum T ss F hp
   have bound : additionalCost ss F≤r := Nat.le_trans (hs.2.2 G ha) budget
   exact ⟨F,by simp [currentQuery,hp,bound],pretest_length_minimum hp G ha⟩
 | rejected =>
   have low := (ForestPretest01.rejected_lower_bound T ss hp).2 G ha
   have large : ¬r≤1 := by omega
   obtain ⟨F,hF,len⟩ := GenericForest.LocalIH.exact_at_current_budget actual r ih T ss G ha budget
   exact ⟨F,by simp [currentQuery,hp,large,hF],len⟩

theorem currentQuery_malformed_iff (actual : Ordinary) (T : Option Tree) (ss : List Tree) (r : Nat) :
 currentQuery actual T ss r=.malformed ↔ proper T ss=false := by
 rw [←ForestPretest01.refused_iff T ss]
 cases hp : ForestPretest01.pretest01 T ss <;> simp [currentQuery,hp]

theorem currentAnswer_sound (actual : Ordinary) (T : Option Tree) (ss : List Tree) (r : Nat)
 {F : Forest} (h : currentAnswer actual T ss r=some F) :
 agrees T ss F=true ∧ additionalCost ss F≤r := by
 unfold currentAnswer at h
 cases he : currentQuery actual T ss r with
 | malformed => simp [he,CurrentResult.answer?] at h
 | answered answer =>
   have ha : answer=some F := by simpa [he,CurrentResult.answer?] using h
   subst answer
   exact currentQuery_sound actual T ss r he

theorem currentAnswer_minimum (actual : Ordinary) (T : Option Tree) (ss : List Tree) (r : Nat)
 (ih : LocalOrdinaryIH r actual) {F : Forest} (h : currentAnswer actual T ss r=some F) :
 ∀ G,agrees T ss G=true → F.length≤G.length := by
 unfold currentAnswer at h
 cases he : currentQuery actual T ss r with
 | malformed => simp [he,CurrentResult.answer?] at h
 | answered answer =>
   have ha : answer=some F := by simpa [he,CurrentResult.answer?] using h
   subst answer
   exact currentQuery_minimum actual T ss r ih he

theorem currentAnswer_complete (actual : Ordinary) (T : Option Tree) (ss : List Tree) (r : Nat)
 (ih : LocalOrdinaryIH r actual) (G : Forest) (ha : agrees T ss G=true) (budget : additionalCost ss G≤r) :
 ∃ F,currentAnswer actual T ss r=some F ∧ F.length≤G.length := by
 obtain ⟨F,hF,len⟩ := currentQuery_complete actual T ss r ih G ha budget
 exact ⟨F,by simp [currentAnswer,hF,CurrentResult.answer?],len⟩
end Universal233.Rule5PaidOrdinary
