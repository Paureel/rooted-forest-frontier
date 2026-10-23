import ChildrenExact
namespace Universal233.Rule5OrdinaryDispatch
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent
open CherryBranching Rule5Local Rule5Classification Rule5FinalClassification Rule5SourceOrientation

inductive Result where
 | selectorRefused
 | paidBuilderRefused
 | answered (answer : Option Forest)
 deriving DecidableEq, Repr

/-- Execute the literal selected branch. The second-case builder refusal stays
distinct from a proved infeasible answer. No proof, geometry or oracle is input. -/
def runSelected (actual : Ordinary) (T S : Tree) (a b q : Nat) : FinalSelection → Result
 | .prefix s => .answered (runChildren actual T S q (localChildren S a b s))
 | .remaining d (.first _ _) => .answered (runChildren actual T S q (firstChildren S a b d))
 | .remaining d (.third _ _) => .answered (runChildren actual T S q (thirdChildren S a b d))
 | .remaining d (.one _) => .answered (Rule5CommonOrdinary.runSelectedCommon actual T S a b d q)
 | .remaining _ (.second _ _) =>
   match Rule5PaidOrdinary.solveSelected actual T S a b q with
   | .builderRefused => .paidBuilderRefused
   | .answered answer => .answered answer

def dispatch (actual : Ordinary) (T S : Tree) (a b q : Nat) : Result :=
 match selectFinal T S a b with
 | none => .selectorRefused
 | some z => runSelected actual T S a b q z

def ExactAnswer (T S : Tree) (q : Nat) (answer : Option Forest) : Prop :=
 (∀F,answer=some F → agreement T S F=true ∧ F.length-1≤q ∧
   ∀G,agreement T S G=true → F.length≤G.length) ∧
 (∀G,agreement T S G=true → G.length-1≤q → ∃F,answer=some F ∧ F.length≤G.length)

theorem children_exact (actual : Ordinary) {T S : Tree} {q : Nat} {cs : List Child}
 (below : BelowIH q actual) (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
 (same : ∀x,x∈leaves T ↔ x∈leaves S)
 (facts : ∀c,c∈cs → ChildFacts S c)
 (cover : ∀G,agreement T S G=true → ∃c,c∈cs ∧ ∃H,feasible T S c H ∧ H.length≤G.length) :
 ExactAnswer T S q (runChildren actual T S q cs) := by
 constructor
 · intro F hF
   exact ⟨(runChildren_sound actual T S q cs hF).1,
     (runChildren_sound actual T S q cs hF).2,
     runChildren_minimum actual below nt ns same facts cover hF⟩
 · exact runChildren_complete actual below nt ns same facts cover

/-- Every final output of the saved actual selector has a concrete executable
current-budget consumer. Only smaller current-budget ordinary IH is used. -/
theorem selected_exact (actual : Ordinary) {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true) {z : FinalSelection}
 (selected : selectFinal T S a b=some z) (q : Nat) (below : BelowIH q actual) :
 ∃answer,runSelected actual T S a b q z=.answered answer ∧ ExactAnswer T S q answer := by
 have prop := properPair_parts (admitted_parts ad).1
 cases z with
 | «prefix» s =>
   have sound := final_selected_sound ch ad selected
   refine ⟨_,rfl,children_exact actual below prop.1 prop.2.1 prop.2.2 ?_ ?_⟩
   · exact fun _ hc => prefix_facts ch sound.1 sound.2 hc
   · exact fun _ ha => local_prefix_cover ch sound.1 sound.2 ha
 | remaining d z =>
   cases z with
   | first u v =>
     refine ⟨_,rfl,children_exact actual below prop.1 prop.2.1 prop.2.2 ?_ ?_⟩
     · exact fun _ hc => first_facts ch ad selected hc
     · exact fun _ ha => selected_first_cover ch ad selected ha
   | third u v =>
     refine ⟨_,rfl,children_exact actual below prop.1 prop.2.1 prop.2.2 ?_ ?_⟩
     · exact fun _ hc => third_facts ch ad selected hc
     · exact fun _ ha => selected_third_cover ch ad selected ha
   | one edge =>
     refine ⟨_,rfl,?_,?_⟩
     · intro F hF
       exact Rule5CommonOrdinary.selected_sound_minimum ch ad selected actual q below hF
     · exact Rule5CommonOrdinary.selected_complete ch ad selected actual q below
   | second u v =>
     cases out : Rule5PaidOrdinary.solveSelected actual T S a b q with
     | builderRefused =>
       exact False.elim (Rule5PaidOrdinary.actual_second_never_builder_refuses actual ch ad selected q out)
     | answered answer =>
       refine ⟨answer,by simp [runSelected,out],?_,?_⟩
       · intro F hF
         have hf : Rule5PaidOrdinary.solveSelected actual T S a b q=.answered (some F) := by rw [out,hF]
         have hs := Rule5PaidOrdinary.solveSelected_sound actual T S a b q hf
         exact ⟨hs.1,hs.2,Rule5PaidOrdinary.solveSelected_minimum actual T S a b q below hf⟩
       · intro G ha budget
         obtain ⟨F,hF,len⟩ := Rule5PaidOrdinary.solveSelected_complete actual ch ad selected q below G ha budget
         exact ⟨F,by simpa [out] using hF,len⟩

theorem admitted_exact (actual : Ordinary) {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true) (q : Nat) (below : BelowIH q actual) :
 ∃answer,dispatch actual T S a b q=.answered answer ∧ ExactAnswer T S q answer := by
 obtain ⟨z,hz,_⟩ := final_classification_complete ch ad
 obtain ⟨answer,run,ex⟩ := selected_exact actual ch ad hz q below
 exact ⟨answer,by simp [dispatch,hz,run],ex⟩

theorem admitted_never_refuses (actual : Ordinary) {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true) (q : Nat) (below : BelowIH q actual) :
 dispatch actual T S a b q≠.selectorRefused ∧ dispatch actual T S a b q≠.paidBuilderRefused := by
 obtain ⟨answer,run,_⟩ := admitted_exact actual ch ad q below
 simp [run]

theorem admitted_sound_minimum (actual : Ordinary) {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true) (q : Nat) (below : BelowIH q actual)
 {F : Forest} (h : dispatch actual T S a b q=.answered (some F)) :
 agreement T S F=true ∧ F.length-1≤q ∧ ∀G,agreement T S G=true → F.length≤G.length := by
 obtain ⟨answer,run,ex⟩ := admitted_exact actual ch ad q below
 have eq : answer=some F := Result.answered.inj (run.symm.trans h)
 exact ex.1 F eq

theorem admitted_complete (actual : Ordinary) {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true) (q : Nat) (below : BelowIH q actual)
 (G : Forest) (ha : agreement T S G=true) (budget : G.length-1≤q) :
 ∃F,dispatch actual T S a b q=.answered (some F) ∧ F.length≤G.length := by
 obtain ⟨answer,run,ex⟩ := admitted_exact actual ch ad q below
 obtain ⟨F,hF,len⟩ := ex.2 G ha budget
 exact ⟨F,by rw [run,hF],len⟩

theorem admitted_feasible_iff (actual : Ordinary) {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true) (q : Nat) (below : BelowIH q actual) :
 (∃F,dispatch actual T S a b q=.answered (some F)) ↔
 ∃G,agreement T S G=true ∧ G.length-1≤q := by
 constructor
 · rintro ⟨F,hF⟩
   have hs := admitted_sound_minimum actual ch ad q below hF
   exact ⟨F,hs.1,hs.2.1⟩
 · rintro ⟨G,ha,budget⟩
   obtain ⟨F,hF,_⟩ := admitted_complete actual ch ad q below G ha budget
   exact ⟨F,hF⟩

theorem admitted_none_iff (actual : Ordinary) {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true) (q : Nat) (below : BelowIH q actual) :
 dispatch actual T S a b q=.answered none ↔ ∀G,agreement T S G=true → q<G.length-1 := by
 obtain ⟨answer,run,ex⟩ := admitted_exact actual ch ad q below
 constructor
 · intro h G ha
   apply Nat.lt_of_not_ge
   intro budget
   obtain ⟨F,hF,_⟩ := ex.2 G ha budget
   rw [hF] at run
   have ee := Result.answered.inj (run.symm.trans h)
   contradiction
 · intro no
   cases answer with
   | none => exact run
   | some F =>
     have hs := ex.1 F rfl
     have bad := no F hs.1
     omega
end Universal233.Rule5OrdinaryDispatch
