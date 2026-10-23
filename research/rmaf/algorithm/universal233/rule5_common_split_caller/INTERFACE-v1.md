# Concrete guarded caller interface

`Setup` stores ten actual trees, X,Y, original representatives, explicit fresh
markers, proper original labels, both checked partitions, actual nonroot
subtree cuts and literal restriction/marked construction equations. It stores
no graph/minimum/coverage/reconstruction/saving/work conclusions. The source
dispatcher must construct these actual inputs; this release does not do so.

`runGuarded d q cb : Option (Option Forest)` executes the ordinary outside
depth01 pretest. A found one-cut answer supplies the actual ordinary outside
forest and its globally minimum cost one. Other outcomes return outer none,
meaning REFUSAL to use this source case. It then executes the marked outside
depth01 pretest; a rejected result uses the concrete one-marker-singleton
extension, proved minimum cost two from the rejected lower bound. No depth-two
or free small exact oracle is called.

The actual guarded job list has two entries, ordinary X and marked X, both at
q-1 when q>0, and is empty at q=0. The callback IH is only BoundedExact on
those exact tree/budget invocations. A returned callback forest is an actual
AF within budget and globally minimum; a failed callback excludes every AF
within that actual budget. The theorem does not assume a marked minimum when
the marked callback fails: original crossing projection establishes feasibility
at the tight boundary. No component receives an unearned discount from its
own minimum.

`reconstruct` consumes the literal returned forests. In the stable case it
generates every possible owner pair from their relabelled lists, using each
actual block's original-color filter and actual list erase remainder.
`pickMerge` checks all candidates on the original T,S and selects a minimum.
The proof supplies an actual generated valid candidate and identifies the
SAME selected output's AF and cost. Failed guesses and duplicate values remain
in the paid local candidate list. In the unstable case literal ordinary
concatenation is returned. The program finally checks the original cut budget.

`runGuarded_answer_exact` derives BoundedExact for every actual inner answer
under GuardedIH on actual jobs. `runGuarded_nonrefusal_iff` proves refusal is
absent exactly at outside minimum one. `guarded_job_progress` derives proper
ordinary child pairs and strict q decrease. Actual callback list mass is at
most two*c^(-1), hence at most one for every rational c>=2; at233/100 the
unpruned value is200/233. This pays callbacks, not the local source toll.

No complete ordinary source case, total mutually recursive solver, final cut
once-call or global running-time theorem is exported here. FIRST-GAP-v1.md
prints those obligations where the source dispatcher consumes this subroutine.
