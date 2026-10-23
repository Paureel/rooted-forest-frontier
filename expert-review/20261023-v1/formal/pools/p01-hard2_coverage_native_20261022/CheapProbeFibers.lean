import RetainedAssembly
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge OutputState Universal233 Universal233.CoreProgram
namespace ContactedHard2Survival

theorem family_members_fresh (K A : List Nat) (P : List (List Nat)) : K∈family A P ↔ K∈P ∧ K⊆A := by
 constructor
 · intro member
   have h:=List.mem_filter.mp member
   exact ⟨h.1,(contained_iff K A).mp h.2⟩
 · intro h
   exact List.mem_filter.mpr ⟨h.1,(contained_iff K A).mpr h.2⟩

theorem cheap_A_color_iff (A B D : List Nat) (apart : ∀x,x∈A→x∈B→False)
 (x y : Nat) (xA : x∈A) (yA : y∈A) :
 edgeCheapColor A B D x=edgeCheapColor A B D y ↔ sideColor D x=sideColor D y := by
 have xb : x∉B:=fun h=>apart x xA h
 have yb : y∉B:=fun h=>apart y yA h
 simp only [edgeCheapColor,taggedColor,ite_eq_right xb,ite_eq_right yb,ite_eq_left xA,ite_eq_left yA]
 omega

theorem side_region_color (T : Tree) (A : List Nat) (p : RMAF.Vertex) (inside : Bool)
 (x y : Nat) (hx : x∈PairGeometry.sideLabels A T p inside) (hy : y∈PairGeometry.sideLabels A T p inside) :
 sideColor (PairGeometry.descendants T p) x=sideColor (PairGeometry.descendants T p) y := by
 cases inside with
 | false=>
  have nx : x∉PairGeometry.descendants T p:=by simpa using (List.mem_filter.mp hx).2
  have ny : y∉PairGeometry.descendants T p:=by simpa using (List.mem_filter.mp hy).2
  simp only [sideColor,ite_eq_right nx,ite_eq_right ny]
 | true=>
  have dx : x∈PairGeometry.descendants T p:=by simpa using (List.mem_filter.mp hx).2
  have dy : y∈PairGeometry.descendants T p:=by simpa using (List.mem_filter.mp hy).2
  simp only [sideColor,ite_eq_left dx,ite_eq_left dy]

theorem cheap_probe_A_fibers (T S : Tree) (A B C : List Nat) (p : RMAF.Vertex)
 (parents : partitionCheck (leaves S) [A,B,C]=true) (nd : (leaves S).Nodup)
 (x y : Nat) (xA : x∈A) (yA : y∈A) (xd : x∈PairGeometry.descendants T p) (yn : y∉PairGeometry.descendants T p)
 (o : Output) (member : o∈(generate S (edgeCheapColor A B (PairGeometry.descendants T p)) 3).outputs) :
 ∀K,K∈family A o.partition→∃inside : Bool,∀z,z∈K ↔ z∈PairGeometry.sideLabels A T p inside := by
 let D:=PairGeometry.descendants T p
 have scope:=cheap_probe_saturation S A B C D parents nd x y xA yA xd yn o member
 have mono:=CutRealization.generate_monochromatic S (edgeCheapColor A B D) 3 o member
 have unique:=saturated_color_partition_unique (leaves S) o.partition (edgeCheapColor A B D) [0,1,2,4]
  nd scope.2.1 mono (by decide) (cheap_four_palette S A B C D parents x y xA yA xd yn) scope.2.2.2.1
 have apart:=(partition_parent_apart _ _ _ _ parents).1
 intro K kFamily
 have kp:=(family_members_fresh K A o.partition).mp kFamily
 have nonempty:=partition_nonempty_member _ _ scope.2.1 K kp.1
 have sideMono : LabelMonochromatic (sideColor D) K := by
  intro u v hu hv
  exact (cheap_A_color_iff A B D apart u v (kp.2 hu) (kp.2 hv)).mp (mono K kp.1 u v hu hv)
 obtain ⟨inside,sub⟩:=side_monochrome_in_region T A K p nonempty kp.2 sideMono
 refine ⟨inside,fun z=>⟨fun hz=>sub hz,?_⟩⟩
 intro hz
 obtain ⟨u,uK⟩:=List.exists_mem_of_ne_nil K nonempty
 have zA : z∈A:=(List.mem_filter.mp hz).1
 have zL:=partition_member_labels _ _ parents A (by simp) z zA
 obtain ⟨J,jP,zJ⟩:=checked_covers _ _ scope.2.1 zL
 have eqColor : edgeCheapColor A B D u=edgeCheapColor A B D z :=
  (cheap_A_color_iff A B D apart u z (kp.2 uK) zA).mpr (side_region_color T A p inside u z (sub uK) hz)
 have eq:=unique K kp.1 J jP u uK z zJ eqColor
 exact eq ▸ zJ
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.family_members_fresh
#print axioms ContactedHard2Survival.family_members_fresh
#check @ContactedHard2Survival.cheap_A_color_iff
#print axioms ContactedHard2Survival.cheap_A_color_iff
#check @ContactedHard2Survival.side_region_color
#print axioms ContactedHard2Survival.side_region_color
#check @ContactedHard2Survival.cheap_probe_A_fibers
#print axioms ContactedHard2Survival.cheap_probe_A_fibers
