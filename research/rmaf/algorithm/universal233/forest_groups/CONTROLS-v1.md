# Forest grouping controls pinned before universal proof

2026-10-15. Regime 1. Exact Bool evaluations are kernel `decide`, not a
numerical fit. The expected values below come from explicitly drawn trees.

1. Ordinary target ((0,1),(2,3)), sources [(0,1),(2,3)], groups
   [[0,1],[2,3]]: whole/local agreements true, exact cost 0.
2. Target (At,(Bt,7)) with At=((0,1),2), Bt=((3,4),(5,6)); sources
   [As=(0,(1,2)), (3,5), (4,6), 7]. Groups A=[0,1,2],
   B=[3,4,5,6], C=[7]. A actual forest [[0,1],[2]] costs 1.
   B source pieces overlap in the target (both include Bt's root), yet
   singleton residual forest [[3],[5],[4],[6]] agrees and costs 2.
   Concatenation with C costs exactly 3, and all cross-group current
   source-piece minimal embeddings clear. Local whole-A agreement false.
3. Removing cross-clear: target ((0,1),(2,3)), sources [(0,2),(1,3)].
   Each group agrees locally with its whole source; concatenation false.
4. Replacing Bforest by free target Bt would accept [[3,4,5,6]] at cost0;
   original current Bforest rejects that forest. This is the false consumer.
5. none/[]/[] true, empty Q true, singleton leaf [9] true; reverse group,
   source, block and leaf order on ordinary controls remain accepted.

Fail criteria: any positive equality fails to compile; each of three fixed
false-control files must fail with `is false`; wrong cost2 for example2
must be rejected. Cross-clear omission must fail at target embeddings, free
whole-B must fail at original block ownership. Pin source bytes before run.

Scope: development controls, not an independent proof verification.
