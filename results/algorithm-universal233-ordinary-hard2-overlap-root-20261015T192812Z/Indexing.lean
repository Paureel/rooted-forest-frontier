import Regional

namespace Universal233.MafScheduler
open PaidQueries

theorem answers_indexed [DecidableEq P] [Inhabited A]
    (minimum : P → Nat) (valid : P → A → Prop)
    (js : List (Job P A)) (xs : List (Nat × A))
    (ha : AnswersFor minimum valid js xs) (hn : (js.map Job.problem).Nodup) :
    ∃ f : P → Nat × A, (js.map Job.problem).map f=xs ∧
      ∀ j∈js, (f j.problem).1=minimum j.problem ∧ valid j.problem (f j.problem).2 := by
  induction ha with
  | nil => exact ⟨fun _ => default,rfl,by simp⟩
  | @cons j x js xs hh hrest ih =>
    have hnd := List.nodup_cons.1 hn
    obtain ⟨g,hg,hvalid⟩ := ih hnd.2
    let f : P → Nat × A := fun p => if p=j.problem then x else g p
    have hne : ∀ k∈js, k.problem≠j.problem := by
      intro k hk he
      exact hnd.1 (List.mem_map.2 ⟨k,hk,he⟩)
    refine ⟨f,?_,?_⟩
    · simp only [List.map_cons]
      have htail : (js.map Job.problem).map f=(js.map Job.problem).map g := by
        apply List.map_congr_left
        intro p hp
        obtain ⟨k,hk,rfl⟩ := List.mem_map.1 hp
        simp only [f,hne k hk,ite_false]
      simp only [f,ite_true,htail,hg]
    · intro k hk
      rcases List.mem_cons.1 hk with he | he
      · subst k
        simpa only [f,ite_true] using hh
      · simpa only [f,hne k he,ite_false] using hvalid k he

theorem totalMinimum_keys (minimum : P → Nat) (js : List (Job P A)) :
    totalMinimum minimum js=((js.map Job.problem).map minimum).sum := by
  induction js with
  | nil => rfl
  | cons j js ih => simp [totalMinimum,ih]

theorem indexed_cost_flatten (Q : List (List Nat)) (f : List Nat → Nat × Forest)
    (hcost : ∀ U∈Q, (f U).1=(f U).2.length-1) :
    answerCost (Q.map f)=(Q.map (fun U => (f U).2.length-1)).sum := by
  simp only [answerCost,List.map_map]
  congr 1
  apply List.map_congr_left
  exact hcost

end Universal233.MafScheduler
