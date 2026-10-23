import PrefixChildrenWork
namespace Universal233.Rule5SelectedLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5PendantLocalWork
open CherryBranching CoreWork Rule5Classification Rule5FinalClassification Rule5SourceOrientation

def reverseAuxMeter : RMAF.Vertex→RMAF.Vertex→Measured RMAF.Vertex
 | [],acc=>⟨acc,1⟩
 | x::xs,acc=>let r:=reverseAuxMeter xs (x::acc);⟨r.value,r.work+2⟩

theorem reverse_aux_value (p acc : RMAF.Vertex) :
 (reverseAuxMeter p acc).value=p.reverse++acc := by
 induction p generalizing acc with
 | nil=>rfl
 | cons x xs ih=>simp only [reverseAuxMeter,ih,List.reverse_cons,List.append_assoc,List.singleton_append]

theorem reverse_aux_work (p acc : RMAF.Vertex) :
 (reverseAuxMeter p acc).work=2*p.length+1 := by
 induction p generalizing acc with
 | nil=>rfl
 | cons x xs ih=>simp only [reverseAuxMeter,ih,List.length_cons];omega

def reverseMeter (p : RMAF.Vertex) :=reverseAuxMeter p []
theorem reverse_value (p : RMAF.Vertex) : (reverseMeter p).value=p.reverse := by
 simp only [reverseMeter,reverse_aux_value,List.append_nil]
theorem reverse_work (p : RMAF.Vertex) : (reverseMeter p).work=2*p.length+1 :=reverse_aux_work p []

def siblingEndpointMeter (S : Tree) (q : RMAF.Vertex) : Measured (Option Nat) :=
 let rev:=reverseMeter q
 match rev.value with
 | []=>⟨none,rev.work+1⟩
 | side::parent=>let p:=reverseMeter parent;let t:=subtreeMeter S (p.value++[!side])
  ⟨match t.value with | some (.leaf x)=>some x | _=>none,rev.work+p.work+p.value.length+t.work+5⟩

theorem sibling_endpoint_value (S : Tree) (q : RMAF.Vertex) :
 (siblingEndpointMeter S q).value=siblingEndpoint? S q := by
 simp only [siblingEndpointMeter,siblingEndpoint?,reverse_value,subtree_value]
 generalize h : q.reverse=xs
 cases xs <;> rfl

theorem sibling_endpoint_work (S : Tree) (q : RMAF.Vertex) :
 (siblingEndpointMeter S q).work≤10*q.length+12 := by
 have rev:=reverse_work q
 simp only [siblingEndpointMeter]
 split
 · dsimp only;omega
 · rename_i side parent eq
   have revlen : q.length=parent.length+1 := by
    have h:=congrArg List.length eq
    simpa only [reverse_value,List.length_reverse,List.length_cons] using h
   have p:=reverse_work parent
   have sub:=subtree_work S ((reverseMeter parent).value++[!side])
   simp only [reverse_value,List.length_reverse,List.length_append,List.length_singleton] at sub ⊢
   omega

theorem sibling_endpoint_label (S : Tree) (q : RMAF.Vertex) {x : Nat}
 (sel : (siblingEndpointMeter S q).value=some x) : x∈leaves S := by
 rw [sibling_endpoint_value] at sel
 unfold siblingEndpoint? at sel
 split at sel
 · contradiction
 · rename_i side parent eq
   cases hs : subtree S (parent.reverse++[!side]) with
   | none=>simp [hs] at sel
   | some U=>cases U with
    | node l r=>simp [hs] at sel
    | leaf y=>
     simp only [hs,Option.some.injEq] at sel
     subst x
     have dom:=subtree_labels_payload S (parent.reverse++[!side])
     have labels : (subtreeLabelsMeter S (parent.reverse++[!side])).value=[y] := by
      rw [subtree_labels_value,source_subtree_labels hs];rfl
     exact dom.2 (by rw [labels];simp)

def firstChildrenMeter (S : Tree) (a b : Nat) (d : BadSelection) : Measured (List Child) :=
 let e:=siblingEndpointMeter S d.badArc
 match e.value with
 | none=>⟨[],e.work+1⟩
 | some x=>let s:=singletonChildMeter S x;let p:=pendantChildMeter S a b
  ⟨[s.value,p.value],e.work+s.work+p.work+3⟩

def thirdChildrenMeter (S : Tree) (a b : Nat) (d : BadSelection) : Measured (List Child) :=
 let e:=siblingEndpointMeter S d.badArc
 match e.value with
 | none=>⟨[],e.work+1⟩
 | some x=>let s:=singletonChildMeter S (if x=a then b else a);let p:=pendantChildMeter S a b
  ⟨[s.value,p.value],e.work+s.work+p.work+4⟩

theorem first_children_value (S : Tree) (a b : Nat) (d : BadSelection) :
 (firstChildrenMeter S a b d).value=firstChildren S a b d := by
 simp only [firstChildrenMeter,firstChildren,sibling_endpoint_value,singleton_child_value,pendant_child_value]
 generalize h : siblingEndpoint? S d.badArc=o
 cases o <;> rfl

theorem third_children_value (S : Tree) (a b : Nat) (d : BadSelection) :
 (thirdChildrenMeter S a b d).value=thirdChildren S a b d := by
 simp only [thirdChildrenMeter,thirdChildren,sibling_endpoint_value,singleton_child_value,pendant_child_value,otherEndpoint]
 generalize h : siblingEndpoint? S d.badArc=o
 cases o <;> rfl

def siblingChildrenBudget (n m : Nat) :=10*m+12+singletonChildBudget n+pendantChildBudget n+4

theorem first_children_work (S : Tree) (a b : Nat) (d : BadSelection) :
 (firstChildrenMeter S a b d).work≤siblingChildrenBudget (leaves S).length d.badArc.length := by
 have e:=sibling_endpoint_work S d.badArc
 simp only [firstChildrenMeter]
 split
 · dsimp only;unfold siblingChildrenBudget;omega
 · rename_i x eq
   have s:=singleton_child_work S x
   have p:=pendant_child_work S a b
   dsimp only;unfold siblingChildrenBudget;omega

theorem third_children_work (S : Tree) (a b : Nat) (d : BadSelection) :
 (thirdChildrenMeter S a b d).work≤siblingChildrenBudget (leaves S).length d.badArc.length := by
 have e:=sibling_endpoint_work S d.badArc
 simp only [thirdChildrenMeter]
 split
 · dsimp only;unfold siblingChildrenBudget;omega
 · rename_i x eq
   have s:=singleton_child_work S (if x=a then b else a)
   have p:=pendant_child_work S a b
   dsimp only;unfold siblingChildrenBudget;omega
end Universal233.Rule5SelectedLocalWork
