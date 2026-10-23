import CommonLocalBinding
namespace Universal233.Rule5LocalWork
open RMAF OrdinaryCommonSplit OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Source

theorem erase_labels (H : List Nat) (F : Forest) : ∀x,x∈(F.erase H).flatten →x∈F.flatten := by
 intro x hx
 obtain ⟨B,hB,hx⟩:=List.mem_flatten.1 hx
 exact List.mem_flatten.2 ⟨B,List.mem_of_mem_erase hB,hx⟩

theorem relabel_numeric (f : Nat→Nat) (F : Forest) (M : Nat)
 (cap : ∀x,x∈F.flatten →x≤M) (fee : ∀x,x≤M →f x≤M) :
 ∀x,x∈(relabelForest f F).flatten →x≤M := by
 have flat : (relabelForest f F).flatten=F.flatten.map f := List.map_flatten.symm
 rw [flat]
 intro x hx
 obtain ⟨y,hy,rfl⟩:=List.mem_map.1 hx
 exact fee y (cap y hy)

theorem merge_numeric (X Y : List Nat) (x y rho gamma M : Nat) (FM FN : Forest)
 (fx : x≤M) (fy : y≤M) (fr : rho≤M) (fg : gamma≤M)
 (capM : ∀z,z∈FM.flatten →z≤M) (capN : ∀z,z∈FN.flatten →z≤M)
 {G : Forest} (mem : G∈mergeCandidates X Y x y rho gamma FM FN) :
 ∀z,z∈G.flatten →z≤M := by
 have gm:=relabel_numeric (swap y rho) FM M capM (fun z hz=>swap_bound y rho z M fy fr hz)
 have gn:=relabel_numeric (swap x gamma) FN M capN (fun z hz=>swap_bound x gamma z M fx fg hz)
 unfold mergeCandidates at mem
 obtain ⟨H,hH,row⟩:=List.mem_flatMap.1 mem
 obtain ⟨J,hJ,eq⟩:=List.mem_map.1 row
 rw [←eq]
 intro z hz
 simp only [merged,List.flatten_cons,List.flatten_append,List.mem_append] at hz
 rcases hz with (hz|hz)|(hz|hz)
 · exact gm z (List.mem_flatten.2 ⟨H,hH,(List.mem_filter.1 hz).1⟩)
 · exact gn z (List.mem_flatten.2 ⟨J,hJ,(List.mem_filter.1 hz).1⟩)
 · exact gm z (erase_labels _ _ z hz)
 · exact gn z (erase_labels _ _ z hz)

theorem built_common_numeric (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex) (d : Setup)
 (build : buildSetup T S X Y p=some d) :
 let M:=labelMax (leaves T++leaves S)+2
 d.x≤M ∧ d.y≤M ∧ d.rho≤M ∧ d.gamma≤M ∧
 (∀z,z∈leaves d.mxT →z≤M) ∧ (∀z,z∈leaves d.myT →z≤M) := by
 dsimp only
 let M:=labelMax (leaves T++leaves S)+2
 have ident:=buildSetup_identity T S X Y p d build
 have fresh:=build_fresh T S X Y p d build
 have old : ∀z,z∈leaves d.T →z≤M := by
   rw [ident.1]
   intro z hz
   have :=label_le_max (leaves T++leaves S) z (List.mem_append_left _ hz)
   dsimp [M];omega
 have hx : d.x∈leaves d.T := SourceCoverage.partitionCheck_subset _ _ d.hpT (by simp [d.hx])
 have hy : d.y∈leaves d.T := SourceCoverage.partitionCheck_subset _ _ d.hpT (by simp [d.hy])
 have xcap:=old _ hx
 have ycap:=old _ hy
 have rho : d.rho≤M := by dsimp [M];omega
 have gamma : d.gamma≤M := by dsimp [M];omega
 exact ⟨xcap,ycap,rho,gamma,marked_numeric d.hMXT M old ycap rho,
   marked_numeric d.hMYT M old xcap gamma⟩

/-- Numeric input needed by the scalar checker bill is also discharged from
actual source build and actual returned forests, for every failed owner guess. -/
theorem common_real_numeric (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex) (d : Setup)
 (build : buildSetup T S X Y p=some d) (r : Nat) {FM FY FN : Forest}
 (fm : actual d.mxT d.mxS r=some FM) {e : RMAF.Vertex}
 (pre : DepthOne.pretest01 d.ty d.sy=.found (some e))
 (fy : FY=DepthOne.forest d.sy (some e)) (fn : outsideReply d FY=some FN)
 {G : Forest} (mem : G∈mergeCandidates d.X d.Y d.x d.y d.rho d.gamma FM FN) :
 ∀z,z∈G.flatten →z≤labelMax (leaves T++leaves S)+2 := by
 have bound:=built_common_numeric T S X Y p d build
 dsimp only at bound
 have mf:=closed_payload d.mxT d.mxS r (marked_pair_setup_proper d) fm
 have found:=found_one_minimum d.ty d.sy e pre
 subst FY
 obtain ⟨F,out,aF,_,_⟩:=outsideReply_spec d _ found.1 found.2.1
 have eq : F=FN := Option.some.inj (out.symm.trans fn)
 have nf:=agreement_payload d.myT d.myS F (proper_left_nodup (marked_outside_proper d)) aF
 subst F
 apply merge_numeric d.X d.Y d.x d.y d.rho d.gamma _ FM FN
   bound.1 bound.2.1 bound.2.2.1 bound.2.2.2.1 ?_ ?_ mem
 · intro z hz;exact bound.2.2.2.2.1 z (mf.2.2.1 z hz)
 · intro z hz;exact bound.2.2.2.2.2 z (nf.2.2.1 z hz)

theorem labelMax_cap (L : List Nat) (M : Nat) (cap : ∀x,x∈L →x≤M) : labelMax L≤M := by
 induction L with
 | nil => simp [labelMax]
 | cons x xs ih =>
   have head:=cap x (by simp)
   have tail:=ih (fun z hz=>cap z (by simp [hz]))
   change max x (labelMax xs)≤M
   omega
end Universal233.Rule5LocalWork
