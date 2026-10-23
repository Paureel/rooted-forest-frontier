# Geometry review specification pin

Mathematical inputs before candidate contact are exactly `research/rmaf/spec.json`,
`ALGORITHM-233-UNIVERSAL-TARGET.md`, and `MULTICOLOR-INTEGRATION-v2.md`.
Their current byte identities are recorded in the freeze receipt.

## Claims to test and later consume

1. A nonempty label block's original rooted minimal embedding is the union
   of the unique original paths between its leaves. It equals the binary
   address-prefix hull from their longest common prefix to those leaves.
   Empty blocks have empty hull; singleton hulls consist of the leaf vertex.
   Suppression does not erase original vertices from the consuming hull.
2. Three nonempty connected original tree hulls that pairwise intersect have
   a common vertex. This does not assert a common edge. The selector must use
   actual original vertices and include original-root cases.
3. For nonempty P contained in parent labels D, H(P) avoids removed vertices
   V iff P is contained in one nonempty D-leaf region of H(D) minus V. Retain
   leafless connected components explicitly. Parent-color coverage requires
   V to contain no D leaf; the overlap consumer also requires every removed
   vertex to be in H(D), unlabelled, and nonterminal in that hull.
4. For two distinct nonterminal vertices v,w in H(D), if deletion leaves
   exactly two nonempty D-leaf regions, every nonempty P subset D occupies v
   iff it occupies w. Controls include a nonempty leafless middle component
   and a three-region counterexample to dropping the region hypothesis.
5. In an original-label state, each final piece belongs to one source parent.
   Validity includes disjoint original hulls in target and source, equal
   rooted restrictions, and complete distinct labels. At most one source
   parent may occupy a fixed vertex only under that validity hypothesis.
   A current-component cut address is not automatically an original-source
   cut: actual edges, source identity, nonempty regions and history lifts
   remain explicit requirements.

Sources: `MULTICOLOR-INTEGRATION-v2.md`, Connected three-parent macro and
Explicit graph and runtime debts 1–6; `ALGORITHM-233-UNIVERSAL-TARGET.md`,
Complete candidate to deliver and Proof and verification criteria;
`spec.json:/conventions,/may_assume,/must_not_assume`.

## Allowed and forbidden assumptions

Allow finite ordinary rooted binary tree definitions, unique paths in a tree,
literal original labels, and standard Lean axioms with complete audits.
Do not assume connectedness, region equivalence, coincidence, ownership,
source-core coverage, original cut lifts, hard-case reachability, or a paid
selector/generator merely because a structure field states them.

The six/seven-leaf chain fixtures below are raw ordinary geometry controls.
They have no certified reduction or hard-branch history. They cannot certify
eligibility of a new production macro. The complete source-core, rule scaffold,
history reconstruction, termination and charged algorithm remain open.

## Control and instrument protocol

The literal `CONTROL-PIN.json` is written before implementing or executing the
checker. Exact equality is the only tolerance. Each deliberately wrong
expectation must be rejected while its clean twin passes. No expected answer
may be regenerated from the checker. A failure halts the run and is preserved;
representation-only repairs require new source hashes and an append-only note.

The checker is organized around explicit graph adjacency and breadth-first
unique paths, with a separately expressed address hull and bottom-up rooted
restriction. It imports no prior verifier, candidate or prover modules.
The reviewer has seen the earlier independent graph implementations; that
knowledge and the common mathematical representation are the same lineage,
with no extra independent replication count. New literal controls address
this proof's geometry specifically.

Runtime is unmeasured before the plant pilot. Controls have at most seven
leaves and enumerate only subsets of the named parent labels; no tree-pair
census is licensed. Record timing and the progress unit (completed controls).

Freeze the instrument and controls before execution, then run plants first.
After controls, report instrument readiness only. Wait for the coordinator's
author source/manifest before source contact, proof review, or compilation.
