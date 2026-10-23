import ChildForestBinding
import RecursiveConsumers
import SelectedExact
import OrdinaryBinding
namespace Universal233.Rule5OrdinaryDispatch
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent
open CherryBranching Rule5Local Rule5Classification Rule5FinalClassification
open Rule5SourceOrientation
abbrev Forest := List (List Nat)
abbrev Ordinary := Tree → Tree → Nat → Option Forest
abbrev BelowIH := Rule5PaidOrdinary.BelowIH

def accepted (T S : Tree) (q : Nat) (F : Forest) : Bool :=
 agreement T S F && decide (F.length-1≤q)

/-- Literal full-current-source-forest callbacks, once per affordable child. -/
def childAnswers (actual : Ordinary) (T : Tree) (q : Nat) (cs : List Child) : List Forest :=
 cs.filterMap (childCall (OrdinaryDispatch.forestChild actual T) q)

def runChildren (actual : Ordinary) (T S : Tree) (q : Nat) (cs : List Child) : Option Forest :=
 best List.length (accepted T S q) (childAnswers actual T q cs)

/-- Proof-only source properties, established below from the actual selector. -/
def ChildFacts (S : Tree) (c : Child) : Prop :=
 partitionCheck (leaves S) c.partition=true ∧ pairwiseEmbeddings S c.partition=true ∧
 c.paid+1=c.partition.length ∧
 c.sourceForest=OutputState.sourceForest S c.partition ∧ 0<c.paid

theorem remaining_strict {q r : Nat} {c : Child}
 (pos : 0<c.paid) (hr : remaining q c=some r) : r<q ∧ c.paid+r=q := by
 unfold remaining at hr
 split at hr
 · have eq := Option.some.inj hr
   omega
 · contradiction

theorem callback_exact (actual : Ordinary) {T S : Tree} {q : Nat}
 (below : BelowIH q actual) (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
 (same : ∀x,x∈leaves T ↔ x∈leaves S) {c : Child} (facts : ChildFacts S c)
 {r : Nat} (hr : remaining q c=some r) :
 OrdinaryDispatch.ExactChildAt T S (OrdinaryDispatch.forestChild actual T) c r := by
 exact OrdinaryDispatch.forest_child_exact_at T S c r actual
   (below r (remaining_strict facts.2.2.2.2 hr).1) nt ns same facts.1 facts.2.1 facts.2.2.2.1

theorem runChildren_sound (actual : Ordinary) (T S : Tree) (q : Nat) (cs : List Child)
 {F : Forest} (h : runChildren actual T S q cs=some F) :
 agreement T S F=true ∧ F.length-1≤q := by
 have hs := (best_spec List.length (accepted T S q) (childAnswers actual T q cs) F h).2.1
 simpa [accepted] using hs

theorem child_answer_cover (actual : Ordinary) {T S : Tree} {q : Nat}
 (below : BelowIH q actual) (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
 (same : ∀x,x∈leaves T ↔ x∈leaves S) {c : Child} (facts : ChildFacts S c)
 (G : Forest) (hG : feasible T S c G) (budget : G.length-1≤q) :
 ∃F, childCall (OrdinaryDispatch.forestChild actual T) q c=some F ∧
 accepted T S q F=true ∧ F.length≤G.length := by
 obtain ⟨r,hr,within⟩ := (remaining_correct q facts.1 facts.2.1 facts.2.2.1).1 ⟨G,hG,budget⟩
 have ex := callback_exact actual below nt ns same facts hr
 obtain ⟨F,hF⟩ := ex.1.2 within
 have hs := ex.2 F hF
 have len := hs.1.2 G hG
 have paid := paid_budget_identity facts.1 facts.2.1 facts.2.2.1 hs.1.1
 have eq := (remaining_strict facts.2.2.2.2 hr).2
 refine ⟨F,?_,?_,len⟩
 · simp [childCall,hr,hF]
 · simp only [accepted,Bool.and_eq_true,decide_eq_true_eq]
   exact ⟨hs.1.1.1,by omega⟩

theorem runChildren_complete (actual : Ordinary) {T S : Tree} {q : Nat} {cs : List Child}
 (below : BelowIH q actual) (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
 (same : ∀x,x∈leaves T ↔ x∈leaves S)
 (facts : ∀c,c∈cs → ChildFacts S c)
 (cover : ∀G,agreement T S G=true → ∃c,c∈cs ∧ ∃H,feasible T S c H ∧ H.length≤G.length)
 (G : Forest) (ha : agreement T S G=true) (budget : G.length-1≤q) :
 ∃F,runChildren actual T S q cs=some F ∧ F.length≤G.length := by
 obtain ⟨c,hc,H,hH,len⟩ := cover G ha
 obtain ⟨K,hK,valid,least⟩ := child_answer_cover actual below nt ns same (facts c hc) H hH (by omega)
 have mem : K∈childAnswers actual T q cs := List.mem_filterMap.2 ⟨c,hc,hK⟩
 obtain ⟨F,hF⟩ := best_exists List.length (accepted T S q) (childAnswers actual T q cs) K mem valid
 have bestlen := (best_spec List.length (accepted T S q) (childAnswers actual T q cs) F hF).2.2 K mem valid
 exact ⟨F,hF,Nat.le_trans bestlen (Nat.le_trans least len)⟩

theorem runChildren_minimum (actual : Ordinary) {T S : Tree} {q : Nat} {cs : List Child}
 (below : BelowIH q actual) (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
 (same : ∀x,x∈leaves T ↔ x∈leaves S)
 (facts : ∀c,c∈cs → ChildFacts S c)
 (cover : ∀G,agreement T S G=true → ∃c,c∈cs ∧ ∃H,feasible T S c H ∧ H.length≤G.length)
 {F : Forest} (h : runChildren actual T S q cs=some F) :
 ∀G,agreement T S G=true → F.length≤G.length := by
 have sound := runChildren_sound actual T S q cs h
 intro G ha
 by_cases budget : G.length-1≤q
 · obtain ⟨H,hH,len⟩ := runChildren_complete actual below nt ns same facts cover G ha budget
   have eq : H=F := Option.some.inj (hH.symm.trans h)
   simpa [eq] using len
 · omega

theorem prefix_facts {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {s : LocalSelection}
 (ch : CherryAt T i a b) (sel : selectLocal T S a b=some s) (ready : s≠.remaining)
 {c : Child} (hc : c∈localChildren S a b s) : ChildFacts S c := by
 have checks := local_prefix_checks ch sel ready hc
 have mat := (local_prefix_source_forest ch sel ready hc).1
 exact ⟨checks.1,checks.2.1,by omega,mat,by omega⟩

theorem first_facts {T S : Tree} {i u v : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (sel : selectFinal T S a b=some (.remaining d (.first u v)))
 {c : Child} (hc : c∈firstChildren S a b d) : ChildFacts S c := by
 have prop := properPair_parts (admitted_parts ad).1
 have checks := branch_checks prop.1 prop.2.1 prop.2.2 ch (first_subbranches ch ad sel hc)
 have sound := final_selected_sound ch ad sel
 have states := selected_child_states ch sound.1 sound.2.1
 have pm : c.paid∈[1,2] := by rw [←states.1]; exact List.mem_map.2 ⟨c,hc,rfl⟩
 have pos : 0<c.paid := by simp only [List.mem_cons,List.mem_singleton] at pm; omega
 exact ⟨checks.1,checks.2.1,checks.2.2,states.2.2 c (Or.inl hc),pos⟩

theorem third_facts {T S : Tree} {i u v : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (sel : selectFinal T S a b=some (.remaining d (.third u v)))
 {c : Child} (hc : c∈thirdChildren S a b d) : ChildFacts S c := by
 have prop := properPair_parts (admitted_parts ad).1
 have checks := branch_checks prop.1 prop.2.1 prop.2.2 ch (third_subbranches ch ad sel hc)
 have sound := final_selected_sound ch ad sel
 have states := selected_child_states ch sound.1 sound.2.1
 have pm : c.paid∈[1,2] := by rw [←states.2.1]; exact List.mem_map.2 ⟨c,hc,rfl⟩
 have pos : 0<c.paid := by simp only [List.mem_cons,List.mem_singleton] at pm; omega
 exact ⟨checks.1,checks.2.1,checks.2.2,states.2.2 c (Or.inr hc),pos⟩
end Universal233.Rule5OrdinaryDispatch
