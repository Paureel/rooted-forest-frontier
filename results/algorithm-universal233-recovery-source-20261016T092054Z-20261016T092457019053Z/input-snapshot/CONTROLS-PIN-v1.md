# Recovery source controls

Frozen before new source-companion execution. Exact expected source values are fixed by construction; all checks remain same-author/tool lineage.

1. Group leaf with origin [false], labels [7], color7: groups=[that group]; groups meter work4, mixedCherry=None; normalize unchanged. Known same-color two-leaf normalization merges labels [7,8] under their parent; unequal colors remain two leaves.
2. Four leaves with colors [0,1,0,1] in two cherries: choose has no unique color and returns the first mixed cherry; a uniform-color tree finishes; a tree with exactly one unique color selects that group's one branch. Meters must match all source values.
3. erase original root returns none, erase a sole selected leaf returns none, erase a leaf from a binary node returns the other subtree, and erase an absent address preserves the tree. These values must remain exact under address comparisons; malformed empty origins exercise guard rejection.
4. Attempt with group.origin=[] refuses before continuation; duplicate cut origin refuses; removal of entire tree refuses. Clean successful attempt evaluates/retains one continuation and increments childAttempts once. False claims that these refusals cost zero must be rejected.
5. q=0 must retain budget-pruned continuation counters. Compare exact source receipt fields (output partitions/cuts, refusals, visited/attempts/pruned) for q=0,1,2 on the constructed trees, including both two-child branches and receipt append work. Never drop failed/pruned paths.
6. Generate singleton leaf7 with constant color7 and q=0 or q=1000: partition[[7]], cuts[], visited1, attempts0, pruned0. Repeated-label input refuses with no coloring calls. Initialization meters must match fromTree/generate values and expose actual color work separately.
7. Final recovery singleton S=leaf7,P=[[7]] returns cuts0/components1. For S=(0,(1,2)),P=[[0],[1,2]], returns cuts1/components2; malformed P refuses. New counter has an explicit proved polynomial envelope; never infer primitive dominance from initialCharge/localCharge declarations.
8. Clean exact arithmetic/source hashes pass. False arithmetic, corrupted normalization/erase/receipt/pruned counts, dropped coloring work, source drift, missing/duplicate producer and custom axiom must be rejected explicitly. Every failed attempt remains retained.

Resource caps: initial process60s, Lean3072MiB, free disk3GiB; raw16MiB, producer8MiB, compressed total256MiB. No scientific dependency rebuild or native/bit claim.
