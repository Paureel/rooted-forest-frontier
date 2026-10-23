import OriginalSides
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge Universal233.CoreGraph

/-- Any original component meeting both sides of an actual cut has the same
marked projection as its canonical color contraction. Both rooted orientations
are proved from original subtree lookup and literal source partitions. -/
theorem original_component_projection (T a : Tree) (X Y B : List Nat) (y m : Nat)
    (nd : (leaves T).Nodup) (hp : partitionCheck (leaves T) [X,Y]=true)
    (edge : OriginalSplit T X Y) (sub : B⊆leaves T)
    (neX : B.filter (X.contains ·)≠[]) (neY : B.filter (Y.contains ·)≠[])
    (hy : y∈Y) (fresh : m∉leaves T) (ha : restrict B T=some a) :
    ∃ z, restrict (B.filter (X.contains ·)++[y]) T=some z ∧
      RootedIso (contract Y m a) (relabel (swap y m) z) := by
  obtain ⟨p,u,hpne,hpu,hside⟩ := edge
  obtain ⟨c,hc⟩ := original_port T u p hpu
  subst T
  have hB := restrict_split_filters (c.plug u) (leaves (c.plug u)) X Y B hp sub
  have disj := split_disjoint _ X Y hp
  rcases hside with sideY | sideX
  · have ctx := c.labels_of_cut u X Y nd hp sideY
    have subK : B.filter (X.contains ·)⊆c.labels := by
      intro x hx;exact (ctx x).2 (List.contains_iff_mem.1 (List.mem_filter.1 hx).2)
    have subL : B.filter (Y.contains ·)⊆leaves u := by
      intro x hx;exact sideY.mem_iff.2 (List.contains_iff_mem.1 (List.mem_filter.1 hx).2)
    obtain ⟨l,hl⟩ := List.exists_mem_of_ne_nil _ neY
    obtain ⟨v,hv⟩ := restriction_exists u (B.filter (Y.contains ·)) ⟨l,subL hl,hl⟩
    obtain ⟨a',z,ha',hz,he⟩ := c.contract_desc_projection u v Y _ _ y m nd
      (fun _ hx => sideY.mem_iff.1 hx)
      (fun x hx => disj x ((ctx x).1 hx)) subK subL (sideY.mem_iff.2 hy) fresh hv
    have hae : a'=a := Option.some.inj (ha'.symm.trans (hB.trans ha))
    subst a'
    exact ⟨z,hz,by rw [he];exact rootedIso_refl _⟩
  · have hp' : partitionCheck (leaves (c.plug u)) [Y,X]=true :=
      BinaryExchange.partition_perm _ [X,Y] [Y,X] (List.Perm.swap X Y []).symm hp
    have ctx := c.labels_of_cut u Y X nd hp' sideX
    have subK : B.filter (X.contains ·)⊆leaves u := by
      intro x hx;exact sideX.mem_iff.2 (List.contains_iff_mem.1 (List.mem_filter.1 hx).2)
    have subL : B.filter (Y.contains ·)⊆c.labels := by
      intro x hx;exact (ctx x).2 (List.contains_iff_mem.1 (List.mem_filter.1 hx).2)
    obtain ⟨k,hk⟩ := List.exists_mem_of_ne_nil _ neX
    obtain ⟨v,hv⟩ := restriction_exists u (B.filter (X.contains ·)) ⟨k,subK hk,hk⟩
    obtain ⟨a',z,ha',hz,hi⟩ := c.contract_root_projection u v Y _ _ y m nd
      (fun x hx => disj x (sideX.mem_iff.1 hx))
      (fun _ hx => (ctx _).1 hx) subK subL neY ((ctx y).2 hy) fresh hv
    have hae : a'=a := Option.some.inj (ha'.symm.trans (hB.trans ha))
    subst a'
    exact ⟨z,hz,hi⟩

/-- The actual rooted topology of every original crossing block projects to
both literal marked inputs. No projected topology premise is supplied. -/
theorem original_crossing_projection (T S : Tree) (X Y B : List Nat) (y m : Nat)
    (ndT : (leaves T).Nodup) (ndS : (leaves S).Nodup)
    (hpT : partitionCheck (leaves T) [X,Y]=true) (hpS : partitionCheck (leaves S) [X,Y]=true)
    (edgeT : OriginalSplit T X Y) (edgeS : OriginalSplit S X Y)
    (subT : B⊆leaves T) (subS : B⊆leaves S)
    (neX : B.filter (X.contains ·)≠[]) (neY : B.filter (Y.contains ·)≠[])
    (hy : y∈Y) (freshT : m∉leaves T) (freshS : m∉leaves S)
    (ha : restrictionAgrees T S B=true) :
    ∃ zT zS, restrict (B.filter (X.contains ·)++[y]) T=some zT ∧
      restrict (B.filter (X.contains ·)++[y]) S=some zS ∧
      RootedIso (relabel (swap y m) zT) (relabel (swap y m) zS) := by
  cases ht : restrict B T <;> cases hs : restrict B S <;> simp only [restrictionAgrees,ht,hs] at ha
  all_goals try contradiction
  rename_i a b
  obtain ⟨zT,hzT,hiT⟩ := original_component_projection T a X Y B y m ndT hpT edgeT
    subT neX neY hy freshT ht
  obtain ⟨zS,hzS,hiS⟩ := original_component_projection S b X Y B y m ndS hpS edgeS
    subS neX neY hy freshS hs
  have hi := contract_iso Y m ((sameShape_correct a b).1 ha)
  exact ⟨zT,zS,hzT,hzS,rootedIso_trans (BinaryExchange.iso_symm hiT) (rootedIso_trans hi hiS)⟩
end OrdinaryCommonSplit
