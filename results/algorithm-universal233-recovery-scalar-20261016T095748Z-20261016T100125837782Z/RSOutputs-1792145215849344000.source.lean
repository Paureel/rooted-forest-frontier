import RSOps
namespace OrdinaryDispatch.RecoveryScalar
open RMAF Universal233 CoreProgram CoreWork

theorem groups_flat_length (t : GTree) : ((groups t).flatMap Group.labels).length≤footprint t := by
 induction t with
 | leaf g=>simp only [groups,List.flatMap_cons,List.flatMap_nil,List.append_nil,footprint];omega
 | node p l r il ir=>simp only [groups,List.flatMap_append,List.length_append,footprint];omega

theorem groups_flat_values (B : Nat) (t : GTree) (h : TreeValues B t) :
 ∀x∈(groups t).flatMap Group.labels,x<B := by
 intro x hx
 obtain ⟨g,hg,hx⟩:=List.mem_flatMap.mp hx
 exact (group_values B t h g hg).1 x hx

structure OutputCap (N B : Nat) (o : Output) : Prop where
 blocks : o.partition.length≤N+1
 cells : ∀ b∈o.partition,b.length≤N ∧ ∀x∈b,x<B
 cuts : o.sourceCuts.length≤N
 addresses : ∀v∈o.sourceCuts,v.length≤N

theorem finish_caps (N B q : Nat) (t : GTree) (d : List Group) (c : List Vertex)
 (h : StateCap N B q t d c) :
 OutputCap N B ⟨d.map Group.labels++[(groups (normalize t)).flatMap Group.labels],c⟩ := by
 have w:=h.within;dsimp only [Within] at w
 have tn:=normalize_footprint t
 have len:=groups_flat_length (normalize t)
 refine ⟨?_,?_,by change c.length≤N;omega,h.cuts⟩
 · simp only [List.length_append,List.length_map,List.length_singleton];omega
 · intro b hb
   rcases List.mem_append.mp hb with hb|hb
   · obtain ⟨g,hg,eq⟩:=List.mem_map.mp hb
     subst b
     have a:=h.detached g hg
     exact ⟨a.2.1,a.1.1⟩
   · have eq:b=(groups (normalize t)).flatMap Group.labels:=by simpa using hb
     subst b
     exact ⟨by omega,groups_flat_values B _ (normalize_values B t h.tree)⟩

theorem attempt_output_caps (f : GTree→List Group→List Vertex→Receipt) (N B : Nat)
 (t : GTree) (d : List Group) (c : List Vertex) (g : Group)
 (hf : ∀next,erase g.origin t=some next→∀o∈(f next (g::d) (g.origin::c)).outputs,OutputCap N B o)
 (o : Output) (ho : o∈(attempt f t d c g).outputs) : OutputCap N B o := by
 unfold attempt at ho
 split at ho
 · simp at ho
 · split at ho
   · simp at ho
   · split at ho
     · simp at ho
     · exact hf _ ‹_› o ho

theorem step_output_caps (f : GTree→List Group→List Vertex→Receipt) (N B q : Nat)
 (t : GTree) (d : List Group) (c : List Vertex) (h : StateCap N B q t d c)
 (hf : ∀g∈groups (normalize t),∀next,erase g.origin (normalize t)=some next→
  ∀o∈(f next (g::d) (g.origin::c)).outputs,OutputCap N B o)
 (o : Output) (ho : o∈(step f t d c).outputs) : OutputCap N B o := by
 cases hc:choose (normalize t) with
 | finish=>
  have eq:o=⟨d.map Group.labels++[(groups (normalize t)).flatMap Group.labels],c⟩:=by simpa [step,hc] using ho
  subst o
  exact finish_caps N B q t d c h
 | refuse why=>simp [step,hc] at ho
 | one g=>exact attempt_output_caps f N B _ d c g (hf g (chosen_one_mem _ g hc)) o (by simpa [step,hc,prefixRoot] using ho)
 | two a b=>
  have mem:=chosen_two_mem _ a b hc
  have hm:o∈(attempt f (normalize t) d c a).outputs ∨ o∈(attempt f (normalize t) d c b).outputs:=by simpa [step,hc,prefixRoot,combine] using ho
  rcases hm with hm|hm
  · exact attempt_output_caps f N B _ d c a (hf a mem.1) o hm
  · exact attempt_output_caps f N B _ d c b (hf b mem.2) o hm

theorem run_output_caps (N B q : Nat) (t : GTree) (d : List Group) (c : List Vertex)
 (h : StateCap N B q t d c) (o : Output) (ho : o∈(run q t d c).outputs) : OutputCap N B o := by
 induction q generalizing t d c o with
 | zero=>exact step_output_caps _ N B 0 t d c h (by intros;simp_all) o ho
 | succ q ih=>
  exact step_output_caps (run q) N B (q+1) t d c h
   (by intro g mem next e o ho;exact ih next (g::d) (g.origin::c) (continuation_caps N B q t d c h g mem next e) o ho) o ho

theorem generate_output_caps (t : Tree) (color : Nat→Nat) (budget B : Nat)
 (labels : ∀x∈leaves t,x<B) (colors : ∀x∈leaves t,color x<B)
 (o : Output) (ho : o∈(generate t color budget).outputs) : OutputCap (inputResource t) B o := by
 unfold generate at ho
 split at ho
 · exact run_output_caps _ _ _ _ _ _ (initial_caps t color budget B labels colors) o ho
 · simp at ho

theorem flatten_length_cap (N : Nat) (P : List (List Nat)) (h : ∀b∈P,b.length≤N) :
 P.flatten.length≤N*P.length := by
 induction P with
 | nil=>simp
 | cons b P ih=>
  have a:=h b (by simp)
  have t:=ih (by intro c hc;exact h c (by simp [hc]))
  simp only [List.flatten_cons,List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one];omega

theorem output_flatten_cap (N B : Nat) (o : Output) (h : OutputCap N B o) :
 o.partition.flatten.length≤N*(N+1) :=
 Nat.le_trans (flatten_length_cap N o.partition (by intro b hb;exact (h.cells b hb).1))
  (Nat.mul_le_mul_left N h.blocks)

theorem blockColor_values (B : Nat) (positive : 0<B) (P : List (List Nat))
 (labels : ∀x∈P.flatten,x<B) (x : Nat) : FinalCutRecovery.blockColor P x<B := by
 induction P with
 | nil=>exact positive
 | cons b P ih=>
  have head:b.headD 0<B:=by
   cases b with
   | nil=>exact positive
   | cons y ys=>exact labels y (by simp)
  have tail:=ih (by intro y hy;exact labels y (by simp [hy]))
  simp only [FinalCutRecovery.blockColor]
  split <;> assumption

/-- Final recovery colors are existing block-head labels or zero. Caller labels
are explicit; partition checking transfers that cap to the supplied blocks. -/
theorem checked_color_caps (t : Tree) (P : List (List Nat)) (L : Nat)
 (hn : (leaves t).Nodup) (hp : partitionCheck (leaves t) P=true)
 (labels : ∀x∈leaves t,x<2^L) :
 ∀x,FinalCutRecovery.blockColor P x<2^L := by
 have perm:=FinalCutRecovery.checked_flatten_perm t P hn hp
 apply blockColor_values (2^L) (Nat.pow_pos (by decide)) P
 intro x hx
 exact labels x (perm.mem_iff.mp hx)
end OrdinaryDispatch.RecoveryScalar
