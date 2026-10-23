/- Independent successful-pretest reconstruction. Definitions only from the
   candidate; no author correctness/completeness theorem is invoked. -/
import FastSolve
open RMAF Universal233 OrdinaryDispatch
namespace IndependentReconstruction

 theorem leaf_witness (T : Tree) : ∃ x, x ∈ leaves T := by
  induction T with
  | leaf x => exact ⟨x,by simp [leaves]⟩
  | node l r ih _ =>
    obtain ⟨x,hx⟩ := ih
    exact ⟨x,by simp [leaves,hx]⟩

 theorem coverage (L : List Nat) (F : List (List Nat))
  (h : partitionCheck L F=true) {x : Nat} (hx : x∈L) : x∈F.flatten := by
  have counts : L.all (fun a => F.flatten.count a == 1)=true := by
    simp only [partitionCheck,Bool.and_eq_true] at h
    exact h.1.2
  have hc : F.flatten.count x=1 := beq_iff_eq.1 (List.all_eq_true.1 counts x hx)
  exact List.count_pos_iff.1 (by omega)

 theorem agreement_positive {T S : Tree} {F : List (List Nat)}
  (h : agreement T S F=true) : 0<F.length := by
  have parts := h
  simp only [agreement,Bool.and_eq_true,and_assoc] at parts
  obtain ⟨x,hx⟩ := leaf_witness T
  have covered := coverage (leaves T) F parts.1 hx
  cases F with
  | nil => simp at covered
  | cons B rest => simp

 theorem restrict_cover (T : Tree) (B : List Nat)
  (cover : ∀ x∈leaves T,x∈B) : restrict B T=some T := by
  induction T with
  | leaf x => simp [restrict,cover x (by simp [leaves])]
  | node l r il ir =>
    have cl : ∀ x∈leaves l,x∈B := fun x hx => cover x (by simp [leaves,hx])
    have cr : ∀ x∈leaves r,x∈B := fun x hx => cover x (by simp [leaves,hx])
    simp [restrict,il cl,ir cr]

 theorem singleton_partition (L M : List Nat) (ne : M≠[])
  (unique : M.Nodup) (same : L.Perm M) : partitionCheck L [M]=true := by
  unfold partitionCheck
  simp only [List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [Bool.and_eq_true]
  constructor
  · constructor
    · simp [ne]
    · apply List.all_eq_true.2
      intro x hx
      exact beq_iff_eq.2 (unique.count_of_mem (same.mem_iff.1 hx))
  · apply List.all_eq_true.2
    intro x hx
    exact List.contains_iff.2 (same.mem_iff.2 hx)

 theorem proper_parts {T S : Tree} (hp : DepthOne.proper T S=true) :
  (leaves T).Nodup ∧ (leaves S).Nodup ∧ (leaves T).Perm (leaves S) := by
  simpa only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hp

 theorem full_partition_agreement {T S : Tree} (hp : DepthOne.proper T S=true)
  (shape : sameShape T S=true) : agreement T S [leaves S]=true := by
  obtain ⟨_,ns,perm⟩ := proper_parts hp
  have ne : leaves S≠[] := by
    obtain ⟨x,hx⟩ := leaf_witness S
    intro hn
    simp [hn] at hx
  have pt := singleton_partition (leaves T) (leaves S) ne ns perm
  have ps := singleton_partition (leaves S) (leaves S) ne ns (.refl _)
  have rt := restrict_cover T (leaves S) (fun _ hx=>perm.mem_iff.1 hx)
  have rs := restrict_cover S (leaves S) (fun _ hx=>hx)
  simp [agreement,pt,ps,pairwiseEmbeddings,restrictionAgrees,rt,rs,shape]

 theorem one_block_implies_full {T S : Tree} {B : List Nat}
  (hp : DepthOne.proper T S=true) (h : agreement T S [B]=true) :
  agreement T S [leaves S]=true := by
  have parts := h
  simp only [agreement,Bool.and_eq_true,and_assoc] at parts
  have ct : ∀ x∈leaves T,x∈B := by
    intro x hx
    simpa using coverage (leaves T) [B] parts.1 hx
  have cs : ∀ x∈leaves S,x∈B := by
    intro x hx
    simpa using coverage (leaves S) [B] parts.2.1 hx
  have rt := restrict_cover T B ct
  have rs := restrict_cover S B cs
  have sh : sameShape T S=true := by
    simpa [restrictionAgrees,rt,rs] using parts.2.2.1
  exact full_partition_agreement hp sh

 theorem best_valid {α : Type} (cost : α→Nat) (valid : α→Bool)
  (xs : List α) (out : α) (h : best cost valid xs=some out) : valid out=true := by
  induction xs generalizing out with
  | nil => simp [best] at h
  | cons a rest ih =>
    cases va : valid a with
    | false => exact ih out (by simpa [best,va] using h)
    | true =>
      cases tail : best cost valid rest with
      | none =>
        have eq : a=out := Option.some.inj (by simpa [best,va,tail] using h)
        simpa [←eq] using va
      | some b =>
        by_cases le : cost a≤cost b
        · have eq : a=out := Option.some.inj (by simpa [best,va,tail,le] using h)
          simpa [←eq] using va
        · have eq : b=out := Option.some.inj (by simpa [best,va,tail,le] using h)
          exact eq ▸ ih b tail

 theorem best_zero_head {α : Type} (cost : α→Nat) (valid : α→Bool)
  (head : α) (tail : List α) (hv : valid head=true) (hz : cost head=0) :
  best cost valid (head::tail)=some head := by
  rw [best,hv]
  cases ht : best cost valid tail <;> simp [ht,hz]

 theorem pretest_zero {T S : Tree} (hp : DepthOne.proper T S=true)
  (full : agreement T S [leaves S]=true) : DepthOne.pretest01 T S=.found none := by
  have chose := best_zero_head DepthOne.cutCost
    (fun c=>agreement T S (DepthOne.forest S c)) none ((DepthOne.edges S).map some)
    full rfl
  simpa [DepthOne.pretest01,hp,DepthOne.candidates,chose] using congrArg DepthOne.Result.found (show (none : Option RMAF.Vertex)=none from rfl)

 theorem pretest_valid {T S : Tree} {c : Option RMAF.Vertex}
  (hp : DepthOne.proper T S=true) (hc : DepthOne.pretest01 T S=.found c) :
  agreement T S (DepthOne.forest S c)=true := by
  have selected : best DepthOne.cutCost (fun d=>agreement T S (DepthOne.forest S d))
    (DepthOne.candidates S)=some c := by
    cases hb : best DepthOne.cutCost (fun d=>agreement T S (DepthOne.forest S d))
      (DepthOne.candidates S) with
    | none => simp [DepthOne.pretest01,hp,hb] at hc
    | some d =>
      have eq : d=c := by simpa [DepthOne.pretest01,hp,hb] using hc
      simpa [eq] using hb
  exact best_valid DepthOne.cutCost (fun d=>agreement T S (DepthOne.forest S d)) (DepthOne.candidates S) c selected

 theorem successful_pretest_minimum {T S : Tree} {c : Option RMAF.Vertex}
  (hp : DepthOne.proper T S=true) (hc : DepthOne.pretest01 T S=.found c) :
  agreement T S (DepthOne.forest S c)=true ∧
  (DepthOne.forest S c).length-1=DepthOne.cutCost c ∧
  ∀ F,agreement T S F=true → (DepthOne.forest S c).length≤F.length := by
  refine ⟨pretest_valid hp hc,?_,?_⟩
  · cases c <;> simp [DepthOne.forest,DepthOne.cutCost]
  · intro F hF
    have pos := agreement_positive hF
    cases c with
    | none => simp only [DepthOne.forest,List.length_cons,List.length_nil]; omega
    | some p =>
      have notFull : agreement T S [leaves S]≠true := by
        intro full
        have zero := pretest_zero hp full
        rw [hc] at zero
        cases zero
      have notOne : F.length≠1 := by
        intro one
        obtain ⟨B,rfl⟩ := List.length_eq_one_iff.1 one
        exact notFull (one_block_implies_full hp hF)
      simp only [DepthOne.forest,List.length_cons,List.length_nil]
      omega

 theorem successful_pretest_query {T S : Tree} {c : Option RMAF.Vertex} (q : Nat)
  (hp : DepthOne.proper T S=true) (hc : DepthOne.pretest01 T S=.found c) :
  QueryExact T S q (if DepthOne.cutCost c≤q then some (DepthOne.forest S c) else none) := by
  obtain ⟨af,cost,least⟩ := successful_pretest_minimum hp hc
  by_cases affordable : DepthOne.cutCost c≤q
  · simp only [affordable,if_pos,QueryExact]
    exact ⟨af,by omega,least⟩
  · simp only [affordable,if_neg,QueryExact]
    intro F hF
    have min := least F hF
    omega

 theorem actual_solve_successful_pretest {T S : Tree} {c : Option RMAF.Vertex} (q : Nat)
  (hp : DepthOne.proper T S=true) (hc : DepthOne.pretest01 T S=.found c) :
  QueryExact T S q (FastOrdinary.solve q T S) := by
  rw [FastOrdinary.solve.eq_def]
  simpa only [hp,ite_true,hc] using successful_pretest_query q hp hc

 /- The exact residual obligation is a quantified rejected-pretest arm. This
    hypothesis is intentionally open; no global author exactness is hidden. -/
 def RejectedArm : Prop := ∀ q T S,DepthOne.proper T S=true →
  DepthOne.pretest01 T S=.rejected → QueryExact T S q (FastOrdinary.solve q T S)

 theorem actual_solve_exact_of_rejected (rejected : RejectedArm) (q : Nat) (T S : Tree)
  (hp : DepthOne.proper T S=true) : QueryExact T S q (FastOrdinary.solve q T S) := by
  cases hc : DepthOne.pretest01 T S with
  | refused =>
    unfold DepthOne.pretest01 at hc
    simp only [hp,ite_true] at hc
    split at hc <;> cases hc
  | found c => exact actual_solve_successful_pretest q hp hc
  | rejected => exact rejected q T S hp hc

 theorem positive_control : QueryExact (.leaf 0) (.leaf 0) 0 (some [[0]]) := by
  refine ⟨by decide,by decide,?_⟩
  intro F hF
  exact agreement_positive hF

 theorem false_negative_refuted : ¬ QueryExact (.leaf 0) (.leaf 0) 0 none := by
  intro bad
  have impossible := bad [[0]] (by decide)
  contradiction

 theorem empty_answer_refuted : ¬ QueryExact (.leaf 0) (.leaf 0) 0 (some []) := by
  intro bad
  have no := agreement_positive bad.1
  contradiction
end IndependentReconstruction
