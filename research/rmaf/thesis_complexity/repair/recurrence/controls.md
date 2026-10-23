# Frozen controls and measurement gate

Frozen before constructing the recurrence auditor: parent `repair/controls-frozen.json` is an inherited development control, not an independent oracle. This route additionally freezes these exact hand answers:

1. Standard allowance `w(p,q)=(1+q/2)/2^p`, offset `b(p)=p-3`.
2. G4.1 `(p,q)=(1,0),s=3`: child leading mass `1/4+1/8+3/16=9/16`, target `1/2`; additive total `1-2-3-1=-5`, target `-2`.
3. Change only `s=4`: child mass `1/4+1/16+3/16=1/2`.
4. G4.1 `(1,1),s=3`: child mass `3/8+1/8+1/4=3/4`.
5. Lifted G4.2 `(2,1),s=3`: retained A/B states `(2,1)`, C state `(3,2)` give `3/16+3/64+1/8=23/64`, target `3/8`; offsets sum to `-1`, equal target `-1`.
6. Three-credit discharge `(3,2)` by a cost-two call with inherited `(1,0)` has mass `1/8`, target `1/4`; offset `1-2=-1`, target `0`.
7. Zero exits and one terminal invocation have coefficient 0 and intercept 1. A C continuation with one internal invocation and one empty-credit exit at cost two from C has coefficient `1/4`, intercept `-2`.
8. A C continuation with one internal invocation and one empty-credit exit at cost one has coefficient `1/2`, intercept `-2`; it MUST fail the needed C coefficient `1/4`.
9. For generic frontiers, one invocation plus two cost-one generic exits has coefficient 1 and intercept -5. Omitting its current invocation must be caught by a planted count mismatch.
10. Child-bound composition uses all legal branches, hence remains an upper bound under success short circuit. Finite structural traces do not prove their branches are visited by all short-circuit executions.

Tree controls to recompute with fresh local code: nine-leaf final C has zero legal outgoing calls; thirteen-leaf union gives P={a,x,u}, Q={x,u}; live-two-leaf C has three pendants and only B legal; wrong orientation must be rejected before cuts, and its reversed twin accepted. No general structural claim follows from these controls.

Pilot and gate: exact Fraction arithmetic only; first run the five fixed tree controls and ten hand arithmetic controls, then a bounded table scan. Preserve all failing formulations. Lean kernel checks a separate generic frontier composition and exact rational instances. Fresh nonauthor verification remains a parent-stage requirement; this arm cannot declare VERIFIED-CLOSED.
