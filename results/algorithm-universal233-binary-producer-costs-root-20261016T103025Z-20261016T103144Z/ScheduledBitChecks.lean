import ActualBitChecks
namespace GenericForest.ScalarBits
open RMAF ForestState RestrictionBridge Universal233 Universal233.WholeSourceWork GenericForest.CheckCorrespondence
open GenericForest.FrontierWork Universal233.PaidQueries

def JobBits (L : Nat) (j : Job (Tree×Tree) Forest) : Prop :=
 (∀x∈leaves j.problem.2,labelBits x≤L) ∧
 match j with | .resolved _ _ F=>PayloadLabelBits L F | .hard _=>True

theorem payload_bits_append (L : Nat) (F G : Forest) (f : PayloadLabelBits L F) (g : PayloadLabelBits L G) :
 PayloadLabelBits L (F++G) := by
 intro x hx
 simp only [List.flatten_append,List.mem_append] at hx
 rcases hx with hx|hx
 · exact f x hx
 · exact g x hx

theorem ordinary_payload_source_bits (actual : Ordinary) (bound : ReturnedPayloadBound actual)
 (L : Nat) (p : Tree×Tree) (q : Nat) (F : Forest) (proper : DepthOne.proper p.1 p.2=true)
 (source : ∀x∈leaves p.2,labelBits x≤L) (answer : actual p.1 p.2 q=some F) : PayloadLabelBits L F := by
 have payload:=bound _ _ _ _ proper answer
 simp only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq] at proper
 intro x hx
 exact source x (proper.2.mem_iff.mp (payload.1.mem_iff.mp hx))

theorem run_payload_bits (actual : Ordinary) (bound : ReturnedPayloadBound actual) (L b : Nat)
 (js : List (Job (Tree×Tree) Forest)) (proper : ∀j∈js,JobPayload j) (labels : ∀j∈js,JobBits L j)
 (xs : List (Nat×Forest))
 (answer : (run (fun p b=>(actual p.1 p.2 b).map (fun F=>(F.length-1,F))) b js).answers=some xs) :
 PayloadLabelBits L (xs.flatMap Prod.snd) := by
 induction js generalizing xs with
 | nil=>
  have eq : xs=[]:=by simpa only [run,Option.some.injEq] using answer.symm
  subst xs;intro x hx;simp at hx
 | cons j js ih=>
  have tp : ∀k∈js,JobPayload k:=fun k hk=>proper k (by simp [hk])
  have tl : ∀k∈js,JobBits L k:=fun k hk=>labels k (by simp [hk])
  have hp:=proper j (by simp);have hl:=labels j (by simp)
  cases j with
  | resolved p c F=>
   cases he : (run (fun p b=>(actual p.1 p.2 b).map (fun F=>(F.length-1,F))) b js).answers with
   | none=>simp [run,he] at answer
   | some ys=>
    have eq : xs=(c,F)::ys:=by simpa [run,he] using answer.symm
    subst xs
    exact payload_bits_append L F _ hl.2 (ih tp tl ys he)
  | hard p=>
   cases ha : actual p.1 p.2 b with
   | none=>simp [run,ha] at answer
   | some F=>
    cases he : (run (fun p b=>(actual p.1 p.2 b).map (fun F=>(F.length-1,F))) b js).answers with
    | none=>simp [run,ha,he] at answer
    | some ys=>
     have eq : xs=(F.length-1,F)::ys:=by simpa [run,ha,he] using answer.symm
     subst xs
     exact payload_bits_append L F _ (ordinary_payload_source_bits actual bound L p b F hp.1 hl.1 ha)
      (ih tp tl ys he)

theorem jobs_payload_bits (L : Nat) (t : Tree) (ss : List Tree)
 (actual : ∀s∈ss,componentPair t s=some (pair t s))
 (source : ∀s∈ss,∀x∈leaves s,labelBits x≤L)
 (js : List (Job (Tree×Tree) Forest)) (hjobs : jobs t ss=some js) : ∀j∈js,JobBits L j := by
 induction ss generalizing js with
 | nil=>have eq : js=[]:=by simpa [jobs] using hjobs.symm
        subst js;simp
 | cons s ss ih=>
  have pa:=actual s (by simp)
  cases he : DepthOne.pretest01 (pair t s).1 (pair t s).2 with
  | refused=>simp [jobs,pa,he] at hjobs
  | rejected=>
   cases ht : jobs t ss with
   | none=>simp [jobs,pa,he,ht] at hjobs
   | some ks=>
    have eq : js=.hard (pair t s)::ks:=by simpa [jobs,pa,he,ht] using hjobs.symm
    subst js
    have tailData:=ih (fun r hr=>actual r (by simp [hr])) (fun r hr=>source r (by simp [hr])) ks ht
    intro j hj;rcases List.mem_cons.mp hj with rfl|hj
    · exact ⟨source s (by simp),True.intro⟩
    · exact tailData j hj
  | found c=>
   cases ht : jobs t ss with
   | none=>simp [jobs,pa,he,ht] at hjobs
   | some ks=>
    have eq : js=.resolved (pair t s) (DepthOne.cutCost c) (DepthOne.forest s c)::ks:=by
     simpa [jobs,pa,he,ht] using hjobs.symm
    subst js
    have tailData:=ih (fun r hr=>actual r (by simp [hr])) (fun r hr=>source r (by simp [hr])) ks ht
    have af:=(DepthOne.found_globally_minimum _ _ c he).1
    have part : partitionCheck (leaves s) (DepthOne.forest s c)=true:=by
     simp only [agreement,Bool.and_eq_true] at af
     simpa only [pair] using af.1.1.1.2
    have bits:=payload_bits_partition L (some s) (DepthOne.forest s c) (source s (by simp)) part
    intro j hj;rcases List.mem_cons.mp hj with rfl|hj
    · exact ⟨source s (by simp),bits⟩
    · exact tailData j hj

theorem scheduled_payload_bits (actual : Ordinary) (bound : ReturnedPayloadBound actual) (L : Nat)
 (t : Tree) (ss : List Tree) (q : Nat) (proper : ForestState.proper (some t) ss=true)
 (bits : ∀x∈leaves t,labelBits x≤L) (js : List (Job (Tree×Tree) Forest)) (hjobs : jobs t ss=some js)
 (xs : List (Nat×Forest))
 (answer : (schedule (fun p b=>(actual p.1 p.2 b).map (fun F=>(F.length-1,F))) q js).answers=some xs) :
 PayloadLabelBits L (xs.flatMap Prod.snd) := by
 have jp:=(jobs_payload t ss (fun s hs=>(pair_actual t ss proper s hs).1)
   (fun s hs=>(pair_actual t ss proper s hs).2.2) js hjobs).1
 have jl:=jobs_payload_bits L t ss (fun s hs=>(pair_actual t ss proper s hs).1)
  (proper_input_bits L (some t) ss proper bits).2 js hjobs
 unfold schedule at answer
 split at answer
 · contradiction
 · cases hr : (run (fun p b=>(actual p.1 p.2 b).map (fun F=>(F.length-1,F))) (allocated q js) js).answers with
   | none=>simp [hr] at answer
   | some ys=>
    by_cases hc : answerCost ys≤q
    · have eq : xs=ys:=by simpa [hr,hc] using answer.symm
      subst xs
      exact run_payload_bits actual bound L (allocated q js) js jp jl ys hr
    · simp [hr,hc] at answer

theorem fast_scheduled_binary_checked_bound (L : Nat) (t : Tree) (ss : List Tree) (q : Nat)
 (proper : ForestState.proper (some t) ss=true) (bits : ∀x∈leaves t,labelBits x≤L)
 (js : List (Job (Tree×Tree) Forest)) (hjobs : jobs t ss=some js) (xs : List (Nat×Forest))
 (answer : (schedule (fun p b=>(OrdinaryDispatch.FastOrdinary.solve b p.1 p.2).map (fun F=>(F.length-1,F))) q js).answers=some xs) :
 (bitChecked (checkerWidth L (some t) ss q) (some t) ss q (xs.flatMap Prod.snd)).value=
 checked (some t) ss q (xs.flatMap Prod.snd) ∧
 (bitChecked (checkerWidth L (some t) ss q) (some t) ss q (xs.flatMap Prod.snd)).work≤
 256*(L+14+8*labelBits (stateVolume (some t) ss q+1))*inspectionBill (some t) ss q :=
 binary_checked_inspection_bound L (some t) ss q _ (proper_input_bits L (some t) ss proper bits)
  (scheduled_payload_bits _ fast_returned_payload L t ss q proper bits js hjobs xs answer)
  (scheduled_payload _ fast_returned_payload t ss q proper js hjobs xs answer)
end GenericForest.ScalarBits
