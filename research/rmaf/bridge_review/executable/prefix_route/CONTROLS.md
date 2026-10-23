# Prefix-route controls frozen before source inspection

2026-10-14. False is left, true is right. Addresses below use 0/1 for false/true.
The support candidate is every address on every path from the common prefix
(LCA address) of the selected leaf occurrences to those occurrences.
An absent label contributes no occurrence. Repeated labels contribute all
matching occurrences, rather than choosing one arbitrarily.

Frozen exact cases:
1. t=((0,1),(2,3)), S={0,2}: {epsilon,0,00,1,10}.
2. Same t, S={1}: {01}.
3. Same t, S={0,1}: {0,00,01}.
4. Same t, S={}: {}.
5. Same t, S={9}: {}.
6. t=((7,1),(2,7)), S={7}: {epsilon,0,00,1,11}.
7. Same duplicate-label tree, S={1,9}: {01}; absent 9 must not alter support.
8. t=(8,(8,(8,((0,1),(2,3))))), S={0,1}: {1110,11100,11101}.
9. Same long-initial-path tree, S={0,2}: {111,1110,11100,1111,11110}.

Frozen negative controls:
A. Delete address 0 from case 1. Exact-membership and connectedness checks
must reject the resulting {epsilon,00,1,10}.
B. Replace case 5 expectation by {epsilon}. Exact-membership check must reject.
C. Replace case 6 expectation by {00}, choosing one duplicate occurrence.
Exact-membership check must reject.
D. Include epsilon,1,11 before the true LCA 111 in case 9. Exact-membership
check must reject this unsuppressed initial path.

Source/spec disagreements must be recorded before any expectation changes.
Candidate implementation and source have not been inspected at this freeze.
