import NumericRule5
namespace OrdinaryDispatch.GlobalNumeric
open RMAF ForestState Universal233 Universal233.CherryBranching Universal233.Hard2Overlap
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.FastOrdinary OrdinaryDispatch.Hard2Dispatcher

theorem combined_cap (actual : GenericForest.FrontierWork.Ordinary) {T S : Tree} {c : Candidate}
 {q : Nat} {out : Result} (hp : DepthOne.proper T S=true)
 (hard : CherryBranching.select T S=some (.hard2,c)) (selected : runHard2 T S c=some out)
 (M : Nat) (cap : TreeCap M T) (p : Tree×Tree) (r : Nat)
 (mem : (p,r)∈forestQueries actual (Hard2Combine.combine actual T S c.a c.b q (paidCase actual T S c q out)).calls) :
 PairCap M p.1 p.2 := by
 apply forest_queries_cap actual _ (fun call hc=>combined_queries_proper actual hp hard selected call hc) M _ p r mem
 intro call hc x hx
 exact cap x ((Hard2Size.combined_target_bound actual T S c q out call hc).1 x hx)

theorem disjoint_cap (actual : GenericForest.FrontierWork.Ordinary) {T S : Tree} {c : Candidate}
 (q : Nat) (hp : DepthOne.proper T S=true) (hard : CherryBranching.select T S=some (.hard2,c))
 (M : Nat) (cap : TreeCap M T) (p : Tree×Tree) (r : Nat)
 (mem : (p,r)∈forestQueries actual (Hard2Trace.disjointExecution actual T S c.a c.b q).calls) :
 PairCap M p.1 p.2 := by
 apply forest_queries_cap actual _ (fun call hc=>disjoint_queries_proper actual q hp hard call hc) M _ p r mem
 intro call hc x hx
 exact cap x ((Hard2Size.disjoint_target_bound actual T S c.a c.b q call hc).1 x hx)

theorem hard2_cap (actual : GenericForest.FrontierWork.Ordinary) {T S : Tree} {c d : Candidate}
 (q : Nat) (hp : DepthOne.proper T S=true)
 (forward : CherryBranching.select T S=some (.hard2,c)) (reverse : CherryBranching.select S T=some (.hard2,d))
 (noT : Rule4.select T S=none) (noS : Rule4.select S T=none) (M : Nat) (cap : PairCap M T S)
 (p : Tree×Tree) (r : Nat) (mem : (p,r)∈(hard2Trace actual T S c d q).queries) : PairCap (M+2) p.1 p.2 := by
 have lift (h : PairCap M p.1 p.2) : PairCap (M+2) p.1 p.2 :=
  ⟨treeCap_mono h.1 (by omega),treeCap_mono h.2 (by omega)⟩
 cases selected : runHard2 T S c with
 | none => simp [hard2Trace,selected] at mem
 | some out =>
  cases out with
  | disjoint =>
   by_cases good : (pendantPartition S c.a c.b).all (restrictionAgrees T S)=true
   · simp [hard2Trace,selected,good] at mem
   · by_cases two : ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2
     · have admitted:=(actual_disjoint_admission_iff hp forward reverse noT noS selected).2 two
       apply dispatch_rule5_cap actual (selected_actual forward).1 admitted q M cap
       simpa [hard2Trace,selected,good,two] using mem
     · apply lift
       apply disjoint_cap actual q hp forward M cap.1 p r
       simpa [hard2Trace,selected,good,two] using mem
  | clique v => apply lift;apply combined_cap actual hp forward selected M cap.1 p r;simpa [hard2Trace,selected] using mem
  | four o v w => apply lift;apply combined_cap actual hp forward selected M cap.1 p r;simpa [hard2Trace,selected] using mem
  | diagonal o v w => apply lift;apply combined_cap actual hp forward selected M cap.1 p r;simpa [hard2Trace,selected] using mem
  | pair o choice => apply lift;apply combined_cap actual hp forward selected M cap.1 p r;simpa [hard2Trace,selected] using mem

/-- Literal ordinary trace: the maximum numeric label rises by at most TWO per
ordinary edge, including fresh marked-common jobs. No desired global cap assumed. -/
theorem ordinaryStepTrace_cap (rec : Nat→Tree→Tree→Option CommonForest) (q : Nat)
 {T S : Tree} (hp : DepthOne.proper T S=true) (M : Nat) (cap : PairCap M T S)
 (p : Tree×Tree) (r : Nat) (mem : (p,r)∈(ordinaryStepTrace rec q T S).queries) : PairCap (M+2) p.1 p.2 := by
 have lift (h : PairCap M p.1 p.2) : PairCap (M+2) p.1 p.2 :=
  ⟨treeCap_mono h.1 (by omega),treeCap_mono h.2 (by omega)⟩
 simp only [ordinaryStepTrace,hp,ite_true] at mem
 cases pre : DepthOne.pretest01 T S with
 | refused => simp only [pre,List.not_mem_nil] at mem
 | found c => simp only [pre,List.not_mem_nil] at mem
 | rejected =>
  simp only [pre] at mem
  cases he : early T S with
  | common reverse c =>
   simp only [he] at mem
   split at mem
   · have eq : (p,r)=(commonPair T S reverse c,q) := by simpa only [List.mem_singleton] using mem
     cases eq
     have cap1:=common_pair_cap cap reverse c
     exact ⟨treeCap_mono cap1.1 (by omega),treeCap_mono cap1.2 (by omega)⟩
   · simp only [List.not_mem_nil] at mem
  | one reverse c =>
   have sel : select (Oriented reverse T S).1 (Oriented reverse T S).2=some (.one,c) := by
    simpa only [he,EarlySound] using early_sound T S
   apply lift
   apply children_cap (cutoff rec q) _ _ q _ _ M (oriented_cap cap reverse).1 p r (by simpa only [he] using mem)
   intro x hx
   have eq : x=pendantChild (Oriented reverse T S).2 c.a c.b := by simpa using hx
   subst x
   exact selected_children_proper (oriented_proper hp reverse) sel _ (by simp [branches])
  | high reverse c =>
   have sel : select (Oriented reverse T S).1 (Oriented reverse T S).2=some (.high,c) := by
    simpa only [he,EarlySound] using early_sound T S
   apply lift
   exact children_cap (cutoff rec q) _ _ q _ (fun x hx=>selected_children_proper (oriented_proper hp reverse) sel x hx)
    M (oriented_cap cap reverse).1 p r (by simpa only [he] using mem)
  | rule4Forward s => exact lift (rule4_cap (cutoff rec q) s q M cap p r (by simpa only [he] using mem))
  | rule4Reverse s => exact lift (rule4_cap (cutoff rec q) s q M ⟨cap.2,cap.1⟩ p r (by simpa only [he] using mem))
  | hard2 c d =>
   have facts : select T S=some (.hard2,c) ∧ select S T=some (.hard2,d) ∧
       Rule4.select T S=none ∧ Rule4.select S T=none := by
    simpa only [he,EarlySound] using early_sound T S
   exact hard2_cap (cutoff rec q) q hp facts.1 facts.2.1 facts.2.2.1 facts.2.2.2 M cap p r (by simpa only [he] using mem)
  | refused => simp only [he,List.not_mem_nil] at mem
end OrdinaryDispatch.GlobalNumeric
