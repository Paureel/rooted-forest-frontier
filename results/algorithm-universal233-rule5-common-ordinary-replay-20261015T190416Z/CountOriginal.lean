import MergeStable
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge BinaryExchange

theorem split_complement_labels (labels X Y : List Nat) (hp : partitionCheck labels [X,Y]=true) :
    ∀x∈labels,Y.contains x= !(X.contains x) := by
  intro x hx
  have cover := (split_labels labels X Y hp x).1 hx
  have disj := split_disjoint labels X Y hp x
  by_cases hxX : x∈X
  · have hxY : x∉Y := disj hxX
    simp [hxX,hxY]
  · have hxY : x∈Y := cover.elim (fun h => False.elim (hxX h)) id
    simp [hxX,hxY]

theorem split_clip_bound_of_desc (T S : Tree) (X Y : List Nat) (F : List (List Nat))
    (p : RMAF.Vertex) (b : Bool) (nt : (leaves T).Nodup)
    (hX : ∀x∈leaves T,X.contains x=(PairGeometry.descendants T (p++[b])).contains x)
    (hY : ∀x∈leaves T,Y.contains x= !(X.contains x)) (ha : agreement T S F=true) :
    (clip X F).length+(clip Y F).length≤F.length+1 := by
  have hp := ha
  simp only [agreement,Bool.and_eq_true] at hp
  have labels : ∀x∈F.flatten,x∈leaves T :=
    fun _ hx => Universal233.SourceCoverage.partitionCheck_subset _ F hp.1.1.1.1 hx
  have cX := clip_congr_on_flatten X (PairGeometry.descendants T (p++[b])) F
    (fun x hx => hX x (labels x hx))
  have complement : ∀x∈F.flatten,Y.contains x= !((PairGeometry.descendants T (p++[b])).contains x) := by
    intro x hx
    rw [hY x (labels x hx),hX x (labels x hx)]
  have hc := clips_split_length (PairGeometry.descendants T (p++[b])) Y F complement
  rw [cX,hc]
  exact edge_split_count T S F p b nt ha

theorem actual_split_clip_bound (T S : Tree) (X Y : List Nat) (F : List (List Nat))
    (nt : (leaves T).Nodup) (hp : partitionCheck (leaves T) [X,Y]=true)
    (edge : OriginalSplit T X Y) (ha : agreement T S F=true) :
    (clip X F).length+(clip Y F).length≤F.length+1 := by
  obtain ⟨v,u,hv,hvu,hside⟩ := edge
  let p := v.dropLast
  let b := v.getLast hv
  have he : p++[b]=v := List.dropLast_concat_getLast hv
  rcases hside with sideY | sideX
  · have hy : ∀x∈leaves T,Y.contains x=(PairGeometry.descendants T (p++[b])).contains x := by
      intro x _
      apply Bool.eq_iff_iff.2
      simp only [List.contains_iff_mem,he,descendants_subtree T u v nt hvu]
      exact sideY.mem_iff.symm
    have hp' := BinaryExchange.partition_perm _ [X,Y] [Y,X] (List.Perm.swap X Y []).symm hp
    have h := split_clip_bound_of_desc T S Y X F p b nt hy (split_complement_labels _ Y X hp') ha
    omega
  · have hx : ∀x∈leaves T,X.contains x=(PairGeometry.descendants T (p++[b])).contains x := by
      intro x _
      apply Bool.eq_iff_iff.2
      simp only [List.contains_iff_mem,he,descendants_subtree T u v nt hvu]
      exact sideX.mem_iff.symm
    exact split_clip_bound_of_desc T S X Y F p b nt hx (split_complement_labels _ X Y hp) ha

theorem original_sum_lower (T S tx sx ty sy : Tree) (X Y : List Nat) (m n : Nat)
    (nt : (leaves T).Nodup) (hp : partitionCheck (leaves T) [X,Y]=true)
    (edge : OriginalSplit T X Y)
    (htx : restrict X T=some tx) (hsx : restrict X S=some sx)
    (hty : restrict Y T=some ty) (hsy : restrict Y S=some sy)
    (hm : IsMinimum tx sx m) (hn : IsMinimum ty sy n)
    (F : List (List Nat)) (ha : agreement T S F=true) : m+n≤F.length-1 := by
  have bound := actual_split_clip_bound T S X Y F nt hp edge ha
  have gx := (agreement_clip T S tx sx X F htx hsx ha).1
  have gy := (agreement_clip T S ty sy Y F hty hsy ha).1
  have lx := hm.2 _ gx
  have ly := hn.2 _ gy
  have px := List.length_pos_iff.2 (Universal233.DepthOne.agreement_nonempty tx sx _ gx)
  have py := List.length_pos_iff.2 (Universal233.DepthOne.agreement_nonempty ty sy _ gy)
  omega

theorem equal_sum_has_crossing (T S tx sx ty sy : Tree) (X Y : List Nat) (m n : Nat)
    (hp : partitionCheck (leaves T) [X,Y]=true)
    (htx : restrict X T=some tx) (hsx : restrict X S=some sx)
    (hty : restrict Y T=some ty) (hsy : restrict Y S=some sy)
    (hm : IsMinimum tx sx m) (hn : IsMinimum ty sy n)
    (F : List (List Nat)) (ha : agreement T S F=true) (hc : F.length-1=m+n) :
    ∃B∈F,B.filter (X.contains ·)≠[] ∧ B.filter (Y.contains ·)≠[] := by
  have hparts := ha
  simp only [agreement,Bool.and_eq_true] at hparts
  have labels : ∀x∈F.flatten,x∈leaves T :=
    fun _ hx => Universal233.SourceCoverage.partitionCheck_subset _ F hparts.1.1.1.1 hx
  have comp := split_complement_labels _ X Y hp
  have clipcount := clips_split_length X Y F (fun x hx => comp x (labels x hx))
  have gx := (agreement_clip T S tx sx X F htx hsx ha).1
  have gy := (agreement_clip T S ty sy Y F hty hsy ha).1
  have lx := hm.2 _ gx
  have ly := hn.2 _ gy
  have px := List.length_pos_iff.2 (Universal233.DepthOne.agreement_nonempty tx sx _ gx)
  have py := List.length_pos_iff.2 (Universal233.DepthOne.agreement_nonempty ty sy _ gy)
  apply Classical.byContradiction
  intro noCross
  have noMixed : F.filter (mixed · (X.contains ·))=[] := by
    apply List.filter_eq_nil_iff.2
    intro B hB
    cases hb : mixed B (X.contains ·) with
    | false => simp
    | true =>
      obtain ⟨⟨x,hx,hxx⟩,⟨y,hy,hyx⟩⟩ := (mixed_iff B _).1 hb
      have hyY : Y.contains y=true := by rw [comp y (labels y (List.mem_flatten.2 ⟨B,hB,hy⟩)),hyx];rfl
      exact False.elim (noCross ⟨B,hB,
        (by intro he;have hmem := List.mem_filter.2 ⟨hx,hxx⟩;rw [he] at hmem;contradiction),
        (by intro he;have hmem := List.mem_filter.2 ⟨hy,hyY⟩;rw [he] at hmem;contradiction)⟩)
  have bound := splitAll_length F (X.contains ·)
  rw [noMixed] at bound
  simp only [List.length_nil,Nat.add_zero] at bound
  omega
end OrdinaryCommonSplit
