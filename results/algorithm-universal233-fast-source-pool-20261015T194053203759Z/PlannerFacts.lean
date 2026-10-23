import Planner
namespace Universal233.BothBad
open RMAF CoreProgram SourceCoverage PairAssembly BinaryCheap RankConsumer

theorem entries_sound (q : Nat) (mode : Mode) (xs : List Output) (e : Entry)
    (he : e∈entries q mode xs) :
    e.output∈xs ∧ e.mode=mode ∧ e.output.sourceCuts.length+mode.extra≤q ∧
      e.budget+e.output.sourceCuts.length+mode.extra=q := by
  obtain ⟨o,ho,hmap⟩ := List.mem_filterMap.1 he
  dsimp only [entries] at he
  split at hmap
  · rename_i hbudget
    have heq : e=⟨o,mode,q-o.sourceCuts.length-mode.extra⟩ := Option.some.inj hmap |>.symm
    subst e
    exact ⟨ho,rfl,hbudget,by dsimp;omega⟩
  · simp at hmap

theorem entries_complete (q : Nat) (mode : Mode) (xs : List Output) (o : Output)
    (ho : o∈xs) (hbudget : o.sourceCuts.length+mode.extra≤q) :
    (⟨o,mode,q-o.sourceCuts.length-mode.extra⟩ : Entry)∈entries q mode xs := by
  exact List.mem_filterMap.2 ⟨o,ho,by simp [hbudget]⟩

theorem reuse_exact (S : Tree) (color : Nat → Nat) (hs : (leaves S).Nodup)
    (hr : RankDichotomy.inputRank S color=4) (q : Nat) (hq : 3≤q) :
    reuse S color (fourProbe S color).outputs q=(generate S color q).outputs := by
  have hh := optimized_four_exact S color hs hr q
  simpa [optimizedFourOutputs,reuse,show ¬q<3 by omega] using hh

theorem knownOne_sound (T S : Tree) (A : List Nat) (F : Forest)
    (h : knownOne T S A=some F) :
    ∃ t s p, restrict A T=some t ∧ restrict A S=some s ∧
      DepthOne.pretest01 t s=.found (some p) ∧ F=DepthOne.forest s (some p) ∧
      agreement t s F=true ∧ F.length-1=1 ∧
      CutRealization.RealizedOutput s ⟨F,[p]⟩ ∧
      (∀ H, agreement t s H=true → 1≤H.length-1) := by
  unfold knownOne at h
  cases ht : restrict A T with
  | none => simp [ht] at h
  | some t =>
    cases hs : restrict A S with
    | none => simp [ht,hs] at h
    | some s =>
      cases hp : DepthOne.pretest01 t s with
      | refused => simp [ht,hs,hp] at h
      | rejected => simp [ht,hs,hp] at h
      | found c =>
        cases c with
        | none => simp [ht,hs,hp] at h
        | some p =>
          have he : DepthOne.forest s (some p)=F := by simpa [ht,hs,hp] using h
          obtain ⟨ha,hreal,_,_,hmin⟩ := DepthOne.found_original_minimum t s (some p) hp
          refine ⟨t,s,p,rfl,rfl,hp,he.symm,?_,?_,?_,?_⟩
          · simpa [he] using ha
          · rw [←he];rfl
          · simpa [he,DepthOne.sourceCuts] using hreal
          · simpa only [DepthOne.cutCost] using hmin
end Universal233.BothBad
