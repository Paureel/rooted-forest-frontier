import StableMarker
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge BinaryExchange

theorem clip_cons_length (X B : List Nat) (F : List (List Nat)) :
    (clip X (B::F)).length=(clip X F).length+
      if (B.filter (X.contains ·)).isEmpty then 0 else 1 := by
  cases h : (B.filter (X.contains ·)).isEmpty <;>
    simp only [clip,List.filterMap_cons,clipBlock,h,Bool.false_eq_true,ite_false,ite_true,List.length_cons,Nat.add_zero]

theorem clips_split_length (X Y : List Nat) (F : List (List Nat))
    (hc : ∀x∈F.flatten, Y.contains x= !(X.contains x)) :
    (clip X F).length+(clip Y F).length=(splitAll F (X.contains ·)).length := by
  induction F with
  | nil => simp [clip,splitAll]
  | cons B F ih =>
    have hB : B.filter (Y.contains ·)=B.filter (fun x => !(X.contains x)) :=
      List.filter_congr (by intro x hx;exact hc x (List.mem_append_left _ hx))
    have hF : ∀x∈F.flatten,Y.contains x= !(X.contains x) := by
      intro x hx;exact hc x (List.mem_append_right _ hx)
    rw [clip_cons_length,clip_cons_length,hB]
    have hlen : (split B (X.contains ·)).length=
        (if (B.filter (X.contains ·)).isEmpty then 0 else 1)+
        if (B.filter (fun x => !(X.contains x))).isEmpty then 0 else 1 := by
      cases hx : (B.filter (X.contains ·)).isEmpty <;>
        cases hy : (B.filter (fun x => !(X.contains x))).isEmpty <;>
          simp only [split,yes,no,List.filter_cons,List.filter_nil,hx,hy,
            Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true,List.length_cons,List.length_nil]
    have hs : (splitAll (B::F) (X.contains ·)).length=
        (split B (X.contains ·)).length+(splitAll F (X.contains ·)).length := by
      simp only [splitAll,List.flatMap_cons,List.length_append]
    rw [hs,hlen]
    have hi := ih hF
    omega

theorem clip_congr_on_flatten (X Y : List Nat) (F : List (List Nat))
    (hc : ∀x∈F.flatten,X.contains x=Y.contains x) : clip X F=clip Y F := by
  induction F with
  | nil => rfl
  | cons B F ih =>
    have hfilter : B.filter (X.contains ·)=B.filter (Y.contains ·) :=
      List.filter_congr (by intro x hx;exact hc x (List.mem_append_left _ hx))
    have hhead : clipBlock X B=clipBlock Y B := by simp only [clipBlock,hfilter]
    have htail := ih (by intro x hx;exact hc x (List.mem_append_right _ hx))
    change List.filterMap (clipBlock X) (B::F)=List.filterMap (clipBlock Y) (B::F)
    simp only [List.filterMap_cons,hhead]
    cases hb : clipBlock Y B with
    | none => simpa only [hb,clip] using htail
    | some C => simpa only [hb,clip] using congrArg (C::·) htail

/-- The original agreement, one actual target address and ordinary complement
labels force the paid count lower bound. No bound on crossing pieces is an
input: it is derived from original embedding-disjointness. -/
theorem original_split_lower (T S tx sx ty sy : Tree) (p : RMAF.Vertex) (b : Bool)
    (X Y : List Nat) (m n : Nat)
    (nt : (leaves T).Nodup)
    (hX : ∀x∈leaves T,X.contains x=(PairGeometry.descendants T (p++[b])).contains x)
    (hY : ∀x∈leaves T,Y.contains x= !(X.contains x))
    (htx : restrict X T=some tx) (hsx : restrict X S=some sx)
    (hty : restrict Y T=some ty) (hsy : restrict Y S=some sy)
    (hm : IsMinimum tx sx m) (hn : IsMinimum ty sy n)
    (F : List (List Nat)) (ha : agreement T S F=true) : m+n≤F.length-1 := by
  have hp := ha
  simp only [agreement,Bool.and_eq_true] at hp
  have labels : ∀x∈F.flatten,x∈leaves T :=
    fun x hx => Universal233.SourceCoverage.partitionCheck_subset _ F hp.1.1.1.1 hx
  have hc := clips_split_length X Y F (fun x hx => hY x (labels x hx))
  have hcx := clip_congr_on_flatten X (PairGeometry.descendants T (p++[b])) F
    (fun x hx => hX x (labels x hx))
  have hcom : ∀x∈F.flatten,Y.contains x= !((PairGeometry.descendants T (p++[b])).contains x) := by
    intro x hx
    rw [hY x (labels x hx),hX x (labels x hx)]
  have hcnt := clips_split_length (PairGeometry.descendants T (p++[b])) Y F hcom
  have bound := edge_split_count T S F p b nt ha
  have gx := agreement_clip T S tx sx X F htx hsx ha
  have gy := agreement_clip T S ty sy Y F hty hsy ha
  have lx := hm.2 _ gx.1
  have ly := hn.2 _ gy.1
  have px : 0<(clip X F).length := List.length_pos_iff.2
    (Universal233.DepthOne.agreement_nonempty tx sx _ gx.1)
  have py : 0<(clip Y F).length := List.length_pos_iff.2
    (Universal233.DepthOne.agreement_nonempty ty sy _ gy.1)
  rw [hcx] at hc px lx
  omega
end OrdinaryCommonSplit
