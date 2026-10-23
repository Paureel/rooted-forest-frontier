-- Actual disjoint paid-job completeness from a bounded callback IH.
-- Source-guided structural assembly; no author exactness theorem is applied.
import LocalPaid08
open RMAF ForestState GenericForest ForestGroups
open Universal233 Universal233.PaidQueries Universal233.MafScheduler
namespace ForestContinuation

theorem disjoint_complete_local (K : Nat) (ordinary : Tree→Tree→Nat→Option GenericForest.Forest)
 (ho : ForestMinCompletion.LocalOrdinaryIH K ordinary)
 (t : Tree) (ss : List Tree) (q : Nat) (G : GenericForest.Forest)
 (qK : q≤K) (ha : agrees (some t) ss G=true)
 (hclear : pairwiseEmbeddings t (ss.map leaves)=true) (hq : additionalCost ss G≤q) :
 ∃F,disjointSolve t ss ordinary q=some F ∧ F.length≤G.length := by
 classical
 have hp:=(agrees_parts _ _ _ ha).1
 let keys:=ss.map (pair t)
 have pproper (p : Tree×Tree) (hpk : p∈keys) : DepthOne.proper p.1 p.2=true := by
   obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hpk
   exact (pair_actual t ss hp s hs).2.2
 -- Mathematical minima exist from actual local AFs; no solver exactness is used.
 have existsMin (p : Tree×Tree) (hpk : p∈keys) : ∃n,LocalMinimum p.1 p.2 n := by
   obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hpk
   have hg:=local_pair_forward t ss G ha s hs
   obtain ⟨M,hM,hmin⟩:=ForestMinCompletion.minimum_from_original_AF hg
   exact ⟨M.length-1,⟨M,hM,rfl⟩,fun H hH=>Nat.sub_le_sub_right (hmin H hH) 1⟩
 let m : Tree×Tree→Nat := fun p=>if h:∃n,LocalMinimum p.1 p.2 n then h.choose else 0
 have hm (p : Tree×Tree) (hpk : p∈keys) : LocalMinimum p.1 p.2 (m p) := by
   have he:=existsMin p hpk
   simpa only [m,dite_eq_left he] using he.choose_spec
 obtain ⟨js,hjobs,hkeys,hplan⟩:=jobs_planned_direct t ss m
   (fun s hs=>(pair_actual t ss hp s hs).1)
   (fun s hs=>(pair_actual t ss hp s hs).2.2)
   (fun s hs=>hm (pair t s) (List.mem_map.mpr ⟨s,hs,rfl⟩))
 have jk : ∀j∈js,j.problem∈keys := by
   intro j hj
   change j.problem∈ss.map (pair t)
   rw [←hkeys]
   exact List.mem_map.mpr ⟨j,hj,rfl⟩
 let recPair : Tree×Tree→Nat→Option (Nat×GenericForest.Forest) :=
   fun p b=>(ordinary p.1 p.2 b).map (fun F=>(F.length-1,F))
 let b:=allocated q js
 have bK : b≤K := by
   have bq : b≤q := by dsimp [b,allocated]; omega
   omega
 have recSound : ∀p∈keys,∀c F,recPair p b=some (c,F) → c=m p ∧ PairValid m p F := by
   intro p hpk c F hh
   obtain ⟨H,hH,he⟩:=Option.map_eq_some_iff.mp hh
   have hh':=Prod.mk.inj he
   have hHF : H=F := hh'.2
   subst H
   obtain ⟨hag,hbudget,hmin⟩:=ho.sound _ _ b F bK (pproper p hpk) hH
   have hlow:=(hm p hpk).2 F hag
   obtain ⟨D,hD,hDm⟩:=(hm p hpk).1
   have hupp:=hmin D hD
   have heq : F.length-1=m p := by omega
   exact ⟨by omega,⟨hag,heq⟩⟩
 have totalEq : totalMinimum m js=(ss.map (fun s=>m (pair t s))).sum := by
   rw [totalMinimum_keys,hkeys,List.map_map]
   rfl
 have totalLe : totalMinimum m js≤additionalCost ss G := by
   have hle:=sum_map_le' ss (fun s=>m (pair t s)) (fun s=>(RestrictionBridge.family (leaves s) G).length-1)
     (fun s hs=>(hm (pair t s) (List.mem_map.mpr ⟨s,hs,rfl⟩)).2 _ (local_pair_forward t ss G ha s hs))
   have hbal:=source_blocks_balance _ _ _ ha
   simp only [additionalCost]
   rw [totalEq]
   omega
 have totalq : totalMinimum m js≤q := Nat.le_trans totalLe hq
 have feasible:=feasible_allocation m (PairValid m) js hplan q totalq
 obtain ⟨xs,hrun⟩:=run_complete_fixed recPair b js (by
   intro p hpHard
   have hpk : p∈keys := by simpa only [Job.problem] using jk (.hard p) hpHard
   obtain ⟨D,hD,hDm⟩:=(hm p hpk).1
   obtain ⟨F,hF⟩:=ho.complete _ _ b D bK (pproper p hpk) hD (by have := feasible p hpHard; dsimp [b]; omega)
   exact ⟨(F.length-1,F),by simp [recPair,hF]⟩)
 have hans:=run_sound_fixed m (PairValid m) recPair b js hplan
   (fun p hpHard=>recSound p (by simpa only [Job.problem] using jk (.hard p) hpHard)) xs hrun
 have costeq:=(answers_cost m (PairValid m) js xs hans).1
 have hprune : ¬q<knownCost js+2*pending js := by have := total_lower m (PairValid m) js hplan; omega
 have hxs : (schedule recPair q js).answers=some xs := by
   simp [schedule,hprune,show (run recPair (allocated q js) js).answers=some xs from hrun,
     show answerCost xs≤q by omega]
 have keysND : (js.map Job.problem).Nodup := by
   rw [hkeys]
   apply List.Pairwise.map (R:=fun s r : Tree=>s≠r) (pair t) (fun s r h he=>h (congrArg Prod.snd he))
   exact proper_sources_nodup t ss hp
 obtain ⟨f,hf,hvalid⟩:=answers_indexed m (PairValid m) js xs hans keysND
 have each (s : Tree) (hs : s∈ss) : PairValid m (pair t s) (f (pair t s)).2 := by
   have hpk : pair t s∈js.map Job.problem := by rw [hkeys]; exact List.mem_map.mpr ⟨s,hs,rfl⟩
   obtain ⟨j,hj,hjp⟩:=List.mem_map.mp hpk
   simpa [hjp] using (hvalid j hj).2
 let out : Tree→GenericForest.Forest := fun s=>(f (pair t s)).2
 obtain ⟨hstate,hcost⟩:=local_assemble t ss hp hclear out (fun s hs=>(each s hs).1)
 have flatEq : xs.flatMap Prod.snd=ss.flatMap out := by
   rw [←hf,hkeys,List.map_map,List.flatMap_map]
   rfl
 have sumEq : (ss.map (fun s=>(out s).length-1)).sum=totalMinimum m js := by
   rw [totalEq]
   congr 1
   apply List.map_congr_left
   intro s hs
   exact (each s hs).2
 have hfinalCost : additionalCost ss (xs.flatMap Prod.snd)=totalMinimum m js := by
   rw [flatEq,hcost,sumEq]
 have finalState : agrees (some t) ss (xs.flatMap Prod.snd)=true := by simpa only [flatEq] using hstate
 have ac : accepted (some t) ss q (xs.flatMap Prod.snd)=true := by
   simp only [accepted,Bool.and_eq_true,decide_eq_true_eq]
   exact ⟨finalState,by omega⟩
 refine ⟨xs.flatMap Prod.snd,?_,?_⟩
 · simp only [disjointSolve,disjointAttempt,hjobs,Option.map_some,Option.bind_some]
   change (schedule recPair q js).answers.bind (fun ys=>checked (some t) ss q (ys.flatMap Prod.snd))=_
   simp [hxs,checked,ac]
 · have hlen:=sources_le_blocks _ _ _ finalState
   have hlenG:=sources_le_blocks _ _ _ ha
   simp only [additionalCost] at hfinalCost totalLe
   omega
end ForestContinuation

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ForestContinuation.disjoint_complete_local
#print axioms ForestContinuation.disjoint_complete_local
