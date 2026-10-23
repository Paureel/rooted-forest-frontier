import AdmittedHandler
namespace Universal233.Rule5OrdinaryDispatch
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent
open CherryBranching Rule5Local Rule5Classification Rule5FinalClassification Rule5SourceOrientation

def OriginalCutWitness (S : Tree) (c : Child) : Prop :=
 ∃br : SourceBranch,br.child=c ∧ br.child.paid=br.originalCuts.length ∧
 br.originalCuts.Nodup ∧ ∀e,e∈br.originalCuts → Valid S e ∧ e≠[]

theorem high_cut_witness (S : Tree) (a b : Nat) : OriginalCutWitness S (pendantChild S a b) := by
 refine ⟨highBranch S a b,rfl,rfl,pendantOriginal_nodup S a b,?_⟩
 intro e he
 have h := (cuts_spec S a b e).1 he
 exact ⟨h.1,h.2.1⟩

theorem endpoint_cut_witness {S : Tree} {a b : Nat}
 (ha : a∈leaves S) (hb : b∈leaves S) (ne : a≠b) : OriginalCutWitness S (singletonChild S a) := by
 obtain ⟨q,br,built,cuts,child,paid,leaf,nr⟩ := endpoint_literal ha hb ne
 refine ⟨br,child,paid,?_,?_⟩
 · simp [cuts]
 · intro e he
   have eq : e=q := by simpa [cuts] using he
   subst e
   exact ⟨leaf.valid,nr⟩

theorem pair_cut_witness {S : Tree} {x y : Nat}
 (hx : x∈leaves S) (hy : y∈leaves S) (ne : x≠y) : OriginalCutWitness S (pairChild S x y) := by
 obtain ⟨u,v,br,built,child,cuts,paid,lu,lv,nu,nv,uv⟩ := pair_literal hx hy ne
 refine ⟨br,child,paid,?_,?_⟩
 · simp [cuts,uv]
 · intro e he
   have eq : e=u ∨ e=v := by simpa [cuts] using he
   rcases eq with rfl|rfl
   · exact ⟨lu.valid,nu⟩
   · exact ⟨lv.valid,nv⟩

theorem five_cut_witness {S : Tree} {a b p q : Nat}
 (aS : a∈leaves S) (bS : b∈leaves S) (pS : p∈leaves S) (qS : q∈leaves S)
 (sep : p≠a ∧ p≠b ∧ q≠a ∧ q≠b) {c : Child} (hc : c∈fiveChildren S a b p q) :
 OriginalCutWitness S c := by
 have cs : c=pendantChild S a b ∨ c=pairChild S p a ∨ c=pairChild S p b ∨
   c=pairChild S q a ∨ c=pairChild S q b := by simpa [fiveChildren] using hc
 rcases cs with rfl|rfl|rfl|rfl|rfl
 · exact high_cut_witness S a b
 · exact pair_cut_witness pS aS sep.1
 · exact pair_cut_witness pS bS sep.2.1
 · exact pair_cut_witness qS aS sep.2.2.1
 · exact pair_cut_witness qS bS sep.2.2.2

theorem prefix_cut_witness {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {s : LocalSelection}
 (ch : CherryAt T i a b) (sel : selectLocal T S a b=some s) (ready : s≠.remaining)
 {c : Child} (hc : c∈localChildren S a b s) : OriginalCutWitness S c := by
 have facts := selectLocal_cases sel
 have prop := properPair_parts (admitted_parts facts.1).1
 have aS := (prop.2.2 a).1 (leafAt_label T _ a (cherry_left ch))
 have bS := (prop.2.2 b).1 (leafAt_label T _ b (cherry_right ch))
 cases s with
 | large e =>
   have eq : c=pendantChild S a b := by simpa [localChildren] using hc
   rw [eq]
   exact high_cut_witness S a b
 | two d =>
   have ds := selectSizeTwo_sound facts.2.2
   obtain ⟨_,cpq,_⟩ := sizeTwoCandidate_sound ds
   obtain ⟨Y,Z,hp,he,perm,sep,pX,qX⟩ := admitted_sizeTwo_context facts.1 ch ds
   have labs := hasCherry_labels (actual_hasCherry cpq)
   exact five_cut_witness aS bS labs.1 labs.2 sep hc
 | outside d =>
   have ds := outsideCandidate_sound (selectOutside_sound facts.2.2.2)
   have labs := hasCherry_labels (actual_hasCherry ds.1)
   exact five_cut_witness aS bS labs.1 labs.2 ds.2.2.2.2 hc
 | remaining => exact False.elim (ready rfl)

theorem ordinary_branch_cut_witness {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true) {c : Child} (hc : c∈branches S a b) :
 OriginalCutWitness S c := by
 have prop := properPair_parts (admitted_parts ad).1
 have aS := (prop.2.2 a).1 (leafAt_label T _ a (cherry_left ch))
 have bS := (prop.2.2 b).1 (leafAt_label T _ b (cherry_right ch))
 have ab := cherry_distinct prop.1 ch
 have cs : c=singletonChild S a ∨ c=singletonChild S b ∨ c=pendantChild S a b := by simpa [branches] using hc
 rcases cs with rfl|rfl|rfl
 · exact endpoint_cut_witness aS bS ab
 · exact endpoint_cut_witness bS aS ab.symm
 · exact high_cut_witness S a b

structure ForestJob where
 child : Child
 target : Option Tree
 sources : List Tree
 residual : Nat
 deriving DecidableEq, Repr

def jobFor (T : Tree) (q : Nat) (c : Child) : Option ForestJob :=
 (remaining q c).map fun r => ⟨c,some T,c.sourceForest,r⟩

def forestJobs (T : Tree) (q : Nat) (cs : List Child) : List ForestJob := cs.filterMap (jobFor T q)

/-- This is exactly the callback list consumed by childAnswers. Repeated child
occurrences remain repeated calls, even if their current source states coincide. -/
theorem answers_are_literal_queries (actual : Ordinary) (T : Tree) (q : Nat) (cs : List Child) :
 childAnswers actual T q cs=
 (forestJobs T q cs).filterMap (fun j => GenericForest.solve actual j.target j.sources j.residual) := by
 induction cs with
 | nil => rfl
 | cons c cs ih =>
   cases hr : remaining q c with
   | none => simpa [childAnswers,forestJobs,jobFor,childCall,hr] using ih
   | some r => simpa [childAnswers,forestJobs,jobFor,childCall,hr,OrdinaryDispatch.forestChild] using ih

theorem literal_job_binding {T : Tree} {q : Nat} {cs : List Child} {j : ForestJob}
 (mem : j∈forestJobs T q cs) : j.child∈cs ∧ j.target=some T ∧
 j.sources=j.child.sourceForest ∧ remaining q j.child=some j.residual := by
 obtain ⟨c,hc,hj⟩ := List.mem_filterMap.1 mem
 cases hr : remaining q c with
 | none => simp [jobFor,hr] at hj
 | some r =>
   have eq : (⟨c,some T,c.sourceForest,r⟩ : ForestJob)=j := by simpa [jobFor,hr] using hj
   subst j
   exact ⟨hc,rfl,rfl,hr⟩

theorem actual_job_full_payment {T S : Tree} {q : Nat} {cs : List Child} {j : ForestJob}
 (facts : ∀c,c∈cs → ChildFacts S c)
 (cuts : ∀c,c∈cs → OriginalCutWitness S c)
 (mem : j∈forestJobs T q cs) :
 j.target=some T ∧ j.sources=OutputState.sourceForest S j.child.partition ∧
 partitionCheck (leaves S) j.child.partition=true ∧ pairwiseEmbeddings S j.child.partition=true ∧
 j.residual<q ∧ ∃br : SourceBranch,br.child=j.child ∧ br.originalCuts.Nodup ∧
 (∀e,e∈br.originalCuts → Valid S e ∧ e≠[]) ∧ br.originalCuts.length+j.residual=q := by
 obtain ⟨hc,target,sources,rem⟩ := literal_job_binding mem
 have fs := facts j.child hc
 obtain ⟨br,child,paid,nd,valid⟩ := cuts j.child hc
 have prog := remaining_strict fs.2.2.2.2 rem
 refine ⟨target,sources.trans fs.2.2.2.1,fs.1,fs.2.1,prog.1,br,child,nd,valid,?_⟩
 rw [child] at paid
 omega

theorem prefix_paid_vectors {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {s : LocalSelection}
 (ch : CherryAt T i a b) (sel : selectLocal T S a b=some s) (ready : s≠.remaining) :
 (localChildren S a b s).map Child.paid=
 match s with
 | .large _ => [2]
 | .two _ => [2,2,2,2,2]
 | .outside _ => [2,2,2,2,2]
 | .remaining => [] := by
 have paid : (pendantChild S a b).paid=2 := (admitted_parts (selectLocal_cases sel).1).2.2.2.2
 cases s <;> simp [localChildren,fiveChildren,paid,pairChild,makeChild]

/-- Top-level weighted forest calls preserve the full source debit. The weight
base and every inner ordinary callback's source-work recurrence remain external. -/
def forestWeight (base : Nat) (parentq : Nat) (j : ForestJob) : Nat := base^(parentq-j.residual)

theorem job_weight_is_full_paid {T : Tree} {q : Nat} {cs : List Child} {j : ForestJob}
 (positive : ∀c,c∈cs → 0<c.paid) (mem : j∈forestJobs T q cs) (base : Nat) :
 forestWeight base q j=base^j.child.paid := by
 obtain ⟨hc,_,_,rem⟩ := literal_job_binding mem
 have prog := remaining_strict (positive j.child hc) rem
 have eq : q-j.residual=j.child.paid := by omega
 simp [forestWeight,eq]
end Universal233.Rule5OrdinaryDispatch
