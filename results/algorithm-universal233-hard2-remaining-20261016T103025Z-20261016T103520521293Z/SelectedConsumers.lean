import SelectedExchange
namespace Universal233.Rule5SourceOrientation
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local Rule5Classification Rule5FinalClassification

/-- Literal sibling of the selected original bad arc; no geometry is assumed
by this executable test. None remains an explicit value outside proved inputs. -/
def siblingEndpoint? (S : Tree) (q : RMAF.Vertex) : Option Nat :=
 match q.reverse with
 | [] => none
 | side::parent => match subtree S (parent.reverse++[!side]) with
   | some (.leaf x) => some x
   | _ => none

def otherEndpoint (a b x : Nat) : Nat := if x=a then b else a

def firstChildren (S : Tree) (a b : Nat) (d : BadSelection) : List Child :=
 match siblingEndpoint? S d.badArc with
 | some x => [singletonChild S x,pendantChild S a b]
 | none => []
def thirdChildren (S : Tree) (a b : Nat) (d : BadSelection) : List Child :=
 match siblingEndpoint? S d.badArc with
 | some x => [singletonChild S (otherEndpoint a b x),pendantChild S a b]
 | none => []

theorem siblingEndpoint_fork {S X : Tree} {p : RMAF.Vertex} {s : Bool} {x : Nat}
 (hp : subtree S p=some (fork s (.leaf x) X)) : siblingEndpoint? S (p++[!s])=some x := by
 simp only [siblingEndpoint?,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,List.reverse_reverse,Bool.not_not]
 rw [subtree_append hp,fork_first s (.leaf x) X]

theorem selected_base {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (sel : selectLocal T S a b=some .remaining) (hd : selectBad T S a b=some d) :
 ∃v s t X x y, ((x=a ∧ y=b) ∨ (x=b ∧ y=a)) ∧ siblingEndpoint? S d.badArc=some x ∧
 subtree S v=some (fork t (fork s (.leaf x) X) (.leaf d.c)) ∧
 (cuts S x y=[d.badArc,d.singletonArc] ∨ cuts S x y=[d.singletonArc,d.badArc]) ∧
 subtreeLabels S d.badArc=leaves X ∧ subtreeLabels S d.singletonArc=[d.c] := by
 obtain ⟨h,p,s,t,r,X,x,y,xy,be,cut,hp,hh,ctx⟩ := selected_source_geometry ch sel hd
 have ql : subtreeLabels S d.badArc=leaves X := by
   rw [be]
   exact source_subtree_labels (by rw [subtree_append hp]; exact fork_second s _ _)
 have rl : subtreeLabels S d.singletonArc=[d.c] := source_subtree_labels (selectBad_sound hd).2.2.2.2
 refine ⟨h++[r],s,t,X,x,y,xy,?_,?_,?_,ql,rl⟩
 · rw [be]; exact siblingEndpoint_fork hp
 · rw [subtree_append hh]; exact fork_first r _ _
 · rcases xy with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
   · exact cut
   · rw [cuts_swap]; exact cut

theorem xy_cherry {T : Tree} {i : RMAF.Vertex} {a b x y : Nat}
 (ch : CherryAt T i a b) (xy : (x=a ∧ y=b) ∨ (x=b ∧ y=a)) : ActualCherry T x y := by
 rcases xy with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
 · exact ⟨i,Or.inl ch⟩
 · exact ⟨i,Or.inr ch⟩

theorem xy_pendant (S : Tree) {a b x y : Nat} (xy : (x=a ∧ y=b) ∨ (x=b ∧ y=a)) :
 pendantPartition S x y=pendantPartition S a b := by
 rcases xy with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
 · rfl
 · exact pendantPartition_swap S _ _

theorem selected_first_cover {T S : Tree} {i u w : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (hz : selectFinal T S a b=some (.remaining d (.first u w)))
 {F : List (List Nat)} (ha : agreement T S F=true) :
 ∃c,c∈firstChildren S a b d ∧ ∃G,feasible T S c G ∧ G.length≤F.length := by
 have sound := final_selected_sound ch ad hz
 obtain ⟨v,s,t,X,x,y,xy,sib,base,cut,ql,rl⟩ := selected_base ch sound.1 sound.2.1
 have prop := properPair_parts (admitted_parts ad).1
 have context := selected_bad_context ch sound.1 sound.2.1
 have inc : w∈incident T (subtreeLabels S d.badArc) := by rcases sound.2.2.2.1 with h|h <;> simp [h]
 obtain ⟨W,hW,labs⟩ := region_first_cluster context.1 context.2 inc sound.2.2.2.2.2
 have labs' : ∀z,z∈leaves W ↔ z∈leaves X ∨ z=d.c := by simpa [ql] using labs
 rcases first_exchange prop.1 prop.2.1 prop.2.2 base hW labs' (xy_cherry ch xy) cut ql rl ha with single|⟨G,hG,len,ref⟩
 · exact ⟨singletonChild S x,by simp [firstChildren,sib],F,⟨ha,singleton_refinement ha single⟩,Nat.le_refl _⟩
 · exact ⟨pendantChild S a b,by simp [firstChildren,sib],G,⟨hG,by change Refines G (pendantPartition S a b); rw [←xy_pendant S xy]; exact ref⟩,len⟩

theorem selected_third_cover {T S : Tree} {i u w : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (hz : selectFinal T S a b=some (.remaining d (.third u w)))
 {F : List (List Nat)} (ha : agreement T S F=true) :
 ∃c,c∈thirdChildren S a b d ∧ ∃G,feasible T S c G ∧ G.length≤F.length := by
 have sound := final_selected_sound ch ad hz
 obtain ⟨v,s,t,X,x,y,xy,sib,base,cut,ql,rl⟩ := selected_base ch sound.1 sound.2.1
 have prop := properPair_parts (admitted_parts ad).1
 obtain ⟨z,U,eq,hT⟩ := final_third_root ch ad hz
 have chxy := xy_cherry ch xy
 have exchange : [y]∈F ∨ ∃G,agreement T S G=true ∧ G.length≤F.length ∧ Refines G (pendantPartition S x y) := by
   subst T
   exact third_exchange prop.1 prop.2.1 prop.2.2 base chxy cut ql rl ha
 have other : otherEndpoint a b x=y := by
   have ne := cherry_distinct prop.1 ch
   rcases xy with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [otherEndpoint,ne.symm]
 rcases exchange with single|⟨G,hG,len,ref⟩
 · exact ⟨singletonChild S y,by simp [thirdChildren,sib,other],F,⟨ha,singleton_refinement ha single⟩,Nat.le_refl _⟩
 · exact ⟨pendantChild S a b,by simp [thirdChildren,sib],G,⟨hG,by change Refines G (pendantPartition S a b); rw [←xy_pendant S xy]; exact ref⟩,len⟩
end Universal233.Rule5SourceOrientation
