import HullProfile
namespace FreshClade
open RMAF Universal233.CoreGraph

theorem profile_noC (C D : List Nat) (T : Tree)
 (h : ∀x, x∈leaves T → x∉C) :
 (profile C D T).c=false ∧ (profile C D T).ms=false ∧
 (profile C D T).sm=false ∧ (profile C D T).mm=false := by
 induction T with
 | leaf x => have hx := h x (by simp [leaves]); simp [profile,hx]
 | node l r il ir =>
   have hl := il (fun x hx => h x (by simp [leaves,hx]))
   have hr := ir (fun x hx => h x (by simp [leaves,hx]))
   simp_all [profile,merge]

theorem profile_noD (C D : List Nat) (T : Tree)
 (h : ∀x, x∈leaves T → x∉D) :
 (profile C D T).d=false ∧ (profile C D T).ms=false ∧
 (profile C D T).sm=false ∧ (profile C D T).mm=false := by
 induction T with
 | leaf x => have hx := h x (by simp [leaves]); simp [profile,hx]
 | node l r il ir =>
   have hl := il (fun x hx => h x (by simp [leaves,hx]))
   have hr := ir (fun x hx => h x (by simp [leaves,hx]))
   simp_all [profile,merge]

theorem subtree_leaves {S U : Tree} {p : Vertex} (h : subtree S p=some U) :
 ∀x, x∈leaves U → x∈leaves S := by
 induction p generalizing S with
 | nil => simp [subtree] at h; subst U; exact fun _ hx => hx
 | cons b p ih =>
   cases S with
   | leaf n => simp [subtree] at h
   | node l r =>
     cases b
     · simp [subtree] at h
       exact fun x hx => by simp [leaves,ih h x hx]
     · simp [subtree] at h
       exact fun x hx => by simp [leaves,ih h x hx]

theorem clade_profile (B : List Nat) {S U : Tree} {p : Vertex}
 (unique : (leaves S).Nodup) (h : subtree S p=some U) :
 (profile (B.filter (leaves U).contains) (B.filter (fun x => !(leaves U).contains x)) S).ms=false ∧
 (profile (B.filter (leaves U).contains) (B.filter (fun x => !(leaves U).contains x)) S).mm=false := by
 induction p generalizing S with
 | nil =>
   simp [subtree] at h
   subst U
   have hn := profile_noD (B.filter (leaves S).contains)
    (B.filter (fun x => !(leaves S).contains x)) S (by
     intro x hx hd
     have hd2 := (List.mem_filter.mp hd).2
     have hx2 : (leaves S).contains x=true := List.contains_iff_mem.mpr hx
     simp [hx2] at hd2
     exact hd2 hx)
   exact ⟨hn.2.1,hn.2.2.2⟩
 | cons b p ih =>
   cases S with
   | leaf x => simp [subtree] at h
   | node l r =>
     simp only [leaves,List.nodup_append] at unique
     rcases unique with ⟨ul,ur,disj⟩
     cases b
     · simp [subtree] at h
       have hp := ih ul h
       have nr := profile_noC (B.filter (leaves U).contains)
        (B.filter (fun x => !(leaves U).contains x)) r (by
         intro x hx hc
         have hu : x∈leaves U := (List.mem_filter.mp hc).2 |> List.contains_iff_mem.mp
         exact disj x (subtree_leaves h x hu) x hx rfl)
       simp_all [profile,merge]
     · simp [subtree] at h
       have hp := ih ur h
       have nl := profile_noC (B.filter (leaves U).contains)
        (B.filter (fun x => !(leaves U).contains x)) l (by
         intro x hx hc
         have hu : x∈leaves U := (List.mem_filter.mp hc).2 |> List.contains_iff_mem.mp
         exact disj x hx x (subtree_leaves h x hu) rfl)
       simp_all [profile,merge]

theorem disjoint_eq_not_hits (A B : List Vertex) : disjointVertices A B = !hits A B := by
 induction A with
 | nil => rfl
 | cons v A ih =>
   simp only [disjointVertices,List.all_cons,hits,List.any_cons] at *
   rw [ih]
   cases B.contains v <;> cases A.any B.contains <;> rfl

theorem clade_split_hulls (B : List Nat) {T S U : Tree} {p : Vertex}
 (unique : (leaves S).Nodup) (h : subtree S p=some U)
 (a : restrictionAgrees T S B=true) :
 disjointVertices (minimalVertices (B.filter (leaves U).contains) T)
  (minimalVertices (B.filter (fun x=> !(leaves U).contains x)) T)=true ∧
 disjointVertices (minimalVertices (B.filter (leaves U).contains) S)
  (minimalVertices (B.filter (fun x=> !(leaves U).contains x)) S)=true := by
 have hs := (clade_profile B unique h).2
 have ht := profile_transport B (B.filter (leaves U).contains)
  (B.filter (fun x=> !(leaves U).contains x))
  (fun x hx => (List.mem_filter.mp hx).1)
  (fun x hx => (List.mem_filter.mp hx).1) a
 have hts := congrArg Profile.mm ht
 have os := congrArg Profile.mm (observe_profile (B.filter (leaves U).contains)
  (B.filter (fun x=> !(leaves U).contains x)) S)
 have ot := congrArg Profile.mm (observe_profile (B.filter (leaves U).contains)
  (B.filter (fun x=> !(leaves U).contains x)) T)
 simp only [observe] at os ot
 rw [disjoint_eq_not_hits,disjoint_eq_not_hits,ot,os,hts,hs]
 decide
end FreshClade
