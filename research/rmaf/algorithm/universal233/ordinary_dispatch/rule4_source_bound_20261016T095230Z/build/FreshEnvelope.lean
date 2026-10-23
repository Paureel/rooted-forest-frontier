import ClosedPayload
namespace Universal233.Rule5LocalWork
open RMAF OrdinaryCommonSplit OrdinaryCommonSplit.Caller
open OrdinaryCommonSplit.Source RestrictionBridge

theorem build_fresh (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex) (d : Setup)
 (h : buildSetup T S X Y p=some d) :
 d.rho=labelMax (leaves T++leaves S)+1 ∧ d.gamma=labelMax (leaves T++leaves S)+2 := by
 unfold buildSetup at h
 split at h
 · split at h
   · split at h
     · split at h
       · split at h
         · split at h
           · simp at h
           · split at h
             · split at h
               · dsimp only at h
                 split at h
                 · cases Option.some.inj h;exact ⟨rfl,rfl⟩
                 · simp at h
               · simp at h
             · simp at h
         · simp at h
       · simp at h
     · simp at h
   · simp at h
 · simp at h

theorem swap_bound (a b x M : Nat) (ha : a≤M) (hb : b≤M) (hx : x≤M) :
 swap a b x≤M := by unfold swap;split <;> first | assumption | (split <;> assumption)

theorem restrict_numeric {T U : Tree} {L : List Nat} (hr : restrict L T=some U)
 (M : Nat) (cap : ∀x,x∈leaves T →x≤M) : ∀x,x∈leaves U →x≤M := by
 intro x hx
 exact cap x ((restricted_labels_exact T U L hr).1 hx).1

theorem marked_numeric {T U : Tree} {X : List Nat} {y rho : Nat}
 (hr : marked T X y rho=some U) (M : Nat)
 (cap : ∀x,x∈leaves T →x≤M) (hy : y≤M) (hf : rho≤M) :
 ∀x,x∈leaves U →x≤M := by
 unfold marked at hr
 obtain ⟨V,hv,eq⟩ := Option.map_eq_some_iff.1 hr
 rw [←eq,leaves_relabel]
 intro x hx
 obtain ⟨z,hz,rfl⟩ := List.mem_map.1 hx
 exact swap_bound y rho z M hy hf (restrict_numeric hv M cap z hz)

/-- Actual source builder; both fresh identifiers increase the numeric maximum
by at most two, including all six marked/restricted trees. -/
theorem built_job_numeric (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex) (d : Setup)
 (build : buildSetup T S X Y p=some d) (q : Nat) {j : Job} (mem : j∈paidJobs d q) :
 let M:=labelMax (leaves T++leaves S)+2
 d.rho≤M ∧ d.gamma≤M ∧ (∀x,x∈leaves j.T →x≤M) ∧ (∀x,x∈leaves j.S →x≤M) := by
 dsimp only
 have ident := buildSetup_identity T S X Y p d build
 have fresh := build_fresh T S X Y p d build
 let M:=labelMax (leaves T++leaves S)+2
 have tcap : ∀x,x∈leaves d.T →x≤M := by
   rw [ident.1];intro x hx
   have := label_le_max (leaves T++leaves S) x (List.mem_append_left _ hx)
   dsimp [M];omega
 have scap : ∀x,x∈leaves d.S →x≤M := by
   rw [ident.2.1];intro x hx
   have := label_le_max (leaves T++leaves S) x (List.mem_append_right _ hx)
   dsimp [M];omega
 have rho : d.rho≤M := by dsimp [M];omega
 have gamma : d.gamma≤M := by dsimp [M];omega
 have ymem : d.y∈leaves d.T := SourceCoverage.partitionCheck_subset _ _ d.hpT (by simp [d.hy])
 have ycap := tcap d.y ymem
 have yS : d.y∈leaves d.S := SourceCoverage.partitionCheck_subset _ _ d.hpS (by simp [d.hy])
 refine ⟨rho,gamma,?_⟩
 unfold paidJobs at mem
 split at mem
 · simp at mem
 · have cases : j=⟨d.tx,d.sx,q-1⟩ ∨ j=⟨d.mxT,d.mxS,q-1⟩ := by simpa using mem
   rcases cases with rfl|rfl
   · exact ⟨restrict_numeric d.htx M tcap,restrict_numeric d.hsx M scap⟩
   · exact ⟨marked_numeric d.hMXT M tcap ycap rho,marked_numeric d.hMXS M scap (scap _ yS) rho⟩
end Universal233.Rule5LocalWork
