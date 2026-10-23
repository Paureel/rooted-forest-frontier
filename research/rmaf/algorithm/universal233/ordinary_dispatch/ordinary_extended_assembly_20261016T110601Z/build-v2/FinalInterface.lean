import SourceSpine
namespace Universal233.Rule5FinalClassification
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local Rule5Classification

theorem remaining_bad_arc_unique {T S : Tree} {i e f : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (sel : selectLocal T S a b=some .remaining)
 (em : e∈cuts S a b) (fm : f∈cuts S a b)
 (be : restrictionAgrees T S (subtreeLabels S e)=false)
 (bf : restrictionAgrees T S (subtreeLabels S f)=false) : e=f := by
 have prop := properPair_parts (admitted_parts (selectLocal_cases sel).1).1
 obtain ⟨u,v,c,eq,bad,hc,cl,gc⟩ := remaining_source_status ch sel
 have cS := leafAt_label S v c hc
 have good : restrictionAgrees T S (subtreeLabels S v)=true := by
   rw [cl]; exact singleton_agrees prop.1 prop.2.1 ((prop.2.2 c).2 cS) cS
 have unique {q : RMAF.Vertex} (qm : q∈cuts S a b)
  (bq : restrictionAgrees T S (subtreeLabels S q)=false) : q=u := by
   have qq : q=u ∨ q=v := by rcases eq with eq | eq <;> simpa [eq,or_comm] using qm
   rcases qq with qq | qq
   · exact qq
   · rw [qq,good] at bq; contradiction
 exact (unique em be).trans (unique fm bf).symm

def SourceGeometry (S : Tree) (a b : Nat) (d : BadSelection) : Prop :=
 ∃ h p s t r U x y, ((x=a ∧ y=b) ∨ (x=b ∧ y=a)) ∧
 d.badArc=p++[!s] ∧
 (cuts S a b=[d.badArc,d.singletonArc] ∨ cuts S a b=[d.singletonArc,d.badArc]) ∧
 subtree S p=some (fork s (.leaf x) U) ∧
 subtree S h=some (fork r (fork t (fork s (.leaf x) U) (.leaf d.c)) (.leaf y)) ∧
 LeafContext S (fork r (fork t (fork s (.leaf x) U) (.leaf d.c)) (.leaf y))

theorem selected_source_geometry {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (sel : selectLocal T S a b=some .remaining)
 (hd : selectBad T S a b=some d) : SourceGeometry S a b d := by
 obtain ⟨h,p,s,t,r,U,x,y,f,c,xy,hp,cut,hf,bad,gc,hh,ctx⟩ := remaining_full_source_geometry ch sel
 have ds := selectBad_sound hd
 have em : p++[!s]∈cuts S a b := by rcases cut with eq | eq <;> simp [eq]
 have be : d.badArc=p++[!s] := remaining_bad_arc_unique ch sel ds.1 em ds.2.2.2.1 bad
 have df : d.singletonArc=f := by
   have choices : d.singletonArc=p++[!s] ∨ d.singletonArc=f := by
     rcases cut with eq | eq <;> simpa [eq,or_comm] using ds.2.1
   exact choices.resolve_left (fun eq => ds.2.2.1 (be.trans eq.symm))
 have dc : d.c=c := by
   have hdc := ds.2.2.2.2
   rw [df] at hdc
   exact Tree.leaf.inj (Option.some.inj (hdc.symm.trans hf))
 refine ⟨h,p,s,t,r,U,x,y,xy,be,?_,hp,?_,?_⟩
 · simpa [be,df] using cut
 · simpa [dc] using hh
 · simpa [dc] using ctx

def FinalSound (T S : Tree) (a b : Nat) : FinalSelection → Prop
 | .prefix s => selectLocal T S a b=some s ∧ s≠.remaining
 | .remaining d z => selectLocal T S a b=some .remaining ∧ selectBad T S a b=some d ∧
   SourceGeometry S a b d ∧ BoundarySound T (subtreeLabels S d.badArc) (coreLabels S a b) d.c z

theorem admitted_local_present {T S : Tree} {a b : Nat} (ha : admitted T S a b=true) :
 ∃s,selectLocal T S a b=some s := by
 cases hl : selectLarge T S a b with
 | some e => exact ⟨.large e,by simp [selectLocal,ha,hl]⟩
 | none =>
   cases ht : selectSizeTwo T S a b with
   | some d => exact ⟨.two d,by simp [selectLocal,ha,hl,ht]⟩
   | none =>
     cases ho : selectOutside T S a b with
     | some d => exact ⟨.outside d,by simp [selectLocal,ha,hl,ht,ho]⟩
     | none => exact ⟨.remaining,by simp [selectLocal,ha,hl,ht,ho]⟩

/-- Exhaustive finite source-priority classifier from actual admitted guards.
The remaining result contains proved original geometry, not assumed fields. -/
theorem final_classification_complete {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (ha : admitted T S a b=true) :
 ∃z,selectFinal T S a b=some z ∧ FinalSound T S a b z := by
 obtain ⟨s,hs⟩ := admitted_local_present ha
 cases s with
 | large e => exact ⟨.prefix (.large e),by simp [selectFinal,hs],hs,by simp⟩
 | two d => exact ⟨.prefix (.two d),by simp [selectFinal,hs],hs,by simp⟩
 | outside d => exact ⟨.prefix (.outside d),by simp [selectFinal,hs],hs,by simp⟩
 | remaining =>
   obtain ⟨d,z,hz,hd,sound⟩ := remaining_classifier_complete ch hs
   exact ⟨.remaining d z,hz,hs,hd,selected_source_geometry ch hs hd,sound⟩

theorem final_selected_sound {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {z : FinalSelection}
 (ch : CherryAt T i a b) (ha : admitted T S a b=true)
 (hz : selectFinal T S a b=some z) : FinalSound T S a b z := by
 obtain ⟨w,hw,sw⟩ := final_classification_complete ch ha
 have eq : w=z := Option.some.inj (hw.symm.trans hz)
 subst w; exact sw

/-- Prefix children retain their original source partitions, paid budget and
individual bounded IH contracts through the exhaustive classifier. -/
theorem final_prefix_child_solver {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {s : LocalSelection}
 (ch : CherryAt T i a b) (ha : admitted T S a b=true)
 (hz : selectFinal T S a b=some (.prefix s))
 (solver : Child → Nat → Option (List (List Nat)))
 (ih : ∀c,c∈localChildren S a b s → ExactBoundedChild T S solver c) (k : Nat) :
 OriginalWithin T S k ↔ ∃c,c∈localChildren S a b s ∧ ∃G,childCall solver k c=some G := by
 have hs := final_selected_sound ch ha hz
 exact local_prefix_child_solver ch hs.1 hs.2 solver ih k

theorem final_one_emits {T S : Tree} {i q : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ha : admitted T S a b=true)
 (hz : selectFinal T S a b=some (.remaining d (.one q))) :
 ∃w,commonSplit? T S a b (subtreeLabels S d.badArc)=some w ∧ w.targetArc=q ∧
 Valid T w.targetArc ∧ w.targetArc≠[] ∧ Valid S w.sourceArc ∧ w.sourceArc≠[] ∧
 (∀x,x∈subtreeLabels S w.sourceArc ↔ x∈subtreeLabels S d.badArc) ∧
 ((∀x,x∈leaves T → (x∈subtreeLabels S d.badArc ↔ x∈subtreeLabels T w.targetArc)) ∨
  (∀x,x∈leaves T → (x∈subtreeLabels S d.badArc ↔ x∉subtreeLabels T w.targetArc))) := by
 have hs := final_selected_sound ch ha hz
 have ds := selectBad_sound hs.2.1
 have hn := (properPair_parts (admitted_parts ha).1).1
 exact commonSplit_emits hn hs.2.2.2 ds.1 (by intro x; rfl)

theorem final_third_root {T S : Tree} {i u v : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ha : admitted T S a b=true)
 (hz : selectFinal T S a b=some (.remaining d (.third u v))) :
 ∃s U,u=[s] ∧ T=fork s U (.leaf d.c) := by
 have hs := final_selected_sound ch ha hz
 have sound := hs.2.2.2
 have um : u∈incident T (subtreeLabels S d.badArc) := by rcases sound.1 with eq | eq <;> simp [eq]
 exact third_attachment_actual_root (properPair_parts (admitted_parts ha).1).1 um sound.2.1

end Universal233.Rule5FinalClassification
