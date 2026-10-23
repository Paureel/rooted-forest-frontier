# Controls erratum v1

Issued before implementation or execution and before candidate reading. The original frozen file and its digest are preserved.

- Control 4's proposed nonpartition was transcribed incorrectly: A={a,c} and B={b,d} are disjoint. The intended invalid partition is A={a,c,d}, B={b,d}, sharing d. Use that exact pair for the partition detector. Retain the separately stated degree-three negative unchanged.
- Control 5's numerical values (three nonempty regions, marked optimum 2) are correct, but deletion of adjacent root and child leaves no additional empty component. Delete the claim that this example has an isolated empty region. Add a separate empty-region control: T=((a,b),(c,d)), mark the two cherry roots. Its original root remains an unlabeled isolated component; exactly four nonempty leaf regions remain, marked optimum=3, r=4, residual=0. The planted all-components region counter gives r=5 and must be rejected.

These are hand-spec corrections, not pipeline outputs. No numerical gate is relaxed.
