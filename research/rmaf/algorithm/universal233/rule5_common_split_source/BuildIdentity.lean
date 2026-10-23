import BuildComplete
namespace OrdinaryCommonSplit.Source
open RMAF Caller
theorem buildSetup_identity (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex) (d : Setup)
    (h : buildSetup T S X Y p=some d) : d.T=T ∧ d.S=S ∧ d.X=X ∧ d.Y=Y := by
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
                  · cases Option.some.inj h
                    exact ⟨rfl,rfl,rfl,rfl⟩
                  · simp at h
                · simp at h
              · simp at h
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  · simp at h
end OrdinaryCommonSplit.Source
