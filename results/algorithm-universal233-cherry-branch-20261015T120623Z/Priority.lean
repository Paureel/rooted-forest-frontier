import Consumer
namespace Universal233.CherryBranching
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent

def PrioritySpec (pr : Priority) (c : Candidate) (cs : List Candidate) : Prop :=
 c ∈ cs ∧ match pr with
 | .common => c.originalCuts.length = 0
 | .one => c.originalCuts.length = 1 ∧ ∀ d, d ∈ cs → d.originalCuts.length ≠ 0
 | .high => 3 ≤ c.originalCuts.length ∧ ∀ d, d ∈ cs → d.originalCuts.length ≠ 0 ∧ d.originalCuts.length ≠ 1
 | .hard2 => c.originalCuts.length = 2 ∧ ∀ d, d ∈ cs → d.originalCuts.length = 2

theorem selected_spec {T S : Tree} {pr : Priority} {c : Candidate}
 (h : select T S = some (pr,c)) : PrioritySpec pr c (candidates T S) := by
 have nozero {cs : List Candidate} (hh : cs.find? (fun c => c.originalCuts.isEmpty) = none) :
     ∀ d, d ∈ cs → d.originalCuts.length ≠ 0 := by
   intro d hd hz
   have he : d.originalCuts = [] := List.length_eq_zero_iff.1 hz
   have hn := List.find?_eq_none.1 hh d hd
   simp [he] at hn
 have noone {cs : List Candidate} (hh : cs.find? (fun c => c.originalCuts.length == 1) = none) :
     ∀ d, d ∈ cs → d.originalCuts.length ≠ 1 := by
   intro d hd hz
   have hn := List.find?_eq_none.1 hh d hd
   simp [hz] at hn
 unfold select at h
 cases h0 : (candidates T S).find? (fun c => c.originalCuts.isEmpty) with
 | some d =>
   simp only [h0] at h
   cases h
   refine ⟨List.mem_of_find?_eq_some h0,?_⟩
   have hh := List.find?_some h0
   simpa using List.length_eq_zero_iff.2 (List.isEmpty_iff.1 hh)
 | none =>
   simp only [h0] at h
   cases h1 : (candidates T S).find? (fun c => c.originalCuts.length == 1) with
   | some d =>
     simp only [h1] at h
     cases h
     exact ⟨List.mem_of_find?_eq_some h1,beq_iff_eq.1 (List.find?_some (p := fun c : Candidate => c.originalCuts.length == 1) h1),nozero h0⟩
   | none =>
     simp only [h1] at h
     cases h3 : (candidates T S).find? (fun c => 3 ≤ c.originalCuts.length) with
     | some d =>
       simp only [h3] at h
       cases h
       exact ⟨List.mem_of_find?_eq_some h3,of_decide_eq_true (List.find?_some (p := fun c : Candidate => decide (3 ≤ c.originalCuts.length)) h3),
         fun d hd => ⟨nozero h0 d hd,noone h1 d hd⟩⟩
     | none =>
       simp only [h3] at h
       cases hh : (candidates T S).head? with
       | none => simp [hh] at h
       | some d =>
         simp only [hh,Option.map_some] at h
         cases h
         have alltwo : ∀ d, d ∈ candidates T S → d.originalCuts.length = 2 := by
           intro e he
           have hz := nozero h0 e he
           have ho := noone h1 e he
           have hh := List.find?_eq_none.1 h3 e he
           have hn : ¬3 ≤ e.originalCuts.length := fun hp => hh (decide_eq_true hp)
           omega
         have hm := List.mem_of_head? hh
         exact ⟨hm,alltwo c hm,alltwo⟩

 theorem selected_actual {T S : Tree} {pr : Priority} {c : Candidate}
 (h : select T S = some (pr,c)) :
 CherryAt T c.parent c.a c.b ∧ c.originalCuts = cuts S c.a c.b :=
 candidate_sound (selected_spec h).1
end Universal233.CherryBranching
