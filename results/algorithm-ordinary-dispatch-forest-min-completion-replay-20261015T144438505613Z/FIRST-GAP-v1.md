# Proof target complete; executable transfer separate

The requested minimum-existence and mathematical ghost-totalization claims
are proved in ForestMinimumCompletion. `minimum_from_original_AF` derives
the minimum from an actual AF. `ghost_eq_actual` covers all pairs at b≤K,
including improper pairs. `ghost_global_ordinaryIH` and `ordinaryIH_extension`
consume only LocalOrdinaryIH.

The external consuming obligation is bounded callback congruence for the
actual forest solve/disjoint/schedule code, owned by the parent. No theorem
here claims that the actual callback has a global OrdinaryIH. The control
`high_ghost_can_differ` shows why that conclusion would be too strong.

The ghost has no executable runtime or source-work interpretation. Global
ordinary solver correctness and running-time claims remain outside this
author proof release. All three main milestones remain OPEN; zero improved
base, no novelty or independent acceptance.
