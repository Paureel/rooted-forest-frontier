# Persistent checker caller refinements

The package proves finite-bit refinements of the generic singleton, disjoint-answer, and raw-parent checker continuations. The theorems retain explicit representation equations for the callee-produced inputs. Constructing those represented producer outputs and establishing their stored-label and state invariants remain open, together with production solver assembly, native compiler correspondence, the weighted whole-solver recurrence, and full 2.33 acceptance. Nat work bookkeeping measures the displayed source model; it does not establish native machine cost.

`BinaryCallerActual.lean:8` matches the singleton continuation in the licensed `ForestProgram.lean:30`. The disjoint theorem at line18 matches `GenericForest.disjointSolve` (`ForestProgram.lean:12`), including its answer flattening before the check. The raw-parent theorem at line34 matches the literal branches/filterMap/best expression in `ForestProgram.lean:35`. These proofs use the exact completed persistent-checker import pool; the `ForestProgram` and `RMAF` source bytes were matched to the licensed functional package. No union with the other licensed package pools was assumed. The general differently typed RMAF.agreement/K bridge was not duplicated.

`CallerCaps.lean:59` proves actual capacity width at most `L+Q+2*N+3`. The displayed Caps premises bound target nodes, total source nodes, source count, candidate block count, and candidate cells by N; actual stored label width by L; decoded budget by Q; and stored budget width by Q+1. The budget value and storage premises are separate because padding has a cost. No premise compares q with the reduced leaf count. `payBudget_caps` preserves the original budget and storage caps under an affordable bit-budget payment; `restriction_global_caps` preserves stored label width and the node cap under the actual represented restriction.

`BinaryCallerSetup.lean:6` derives checker setup from its executed leaf copies, bit-cell traversals, forest append, spine counters, and capacity widening. With beta(x)=256*(x+1), the setup polynomial is

```
S = beta(L)*8*(N+1)^2 + beta(L)*13*(N+1)^2
    + 8*Q + 24*L*N + 60*N
    + 16*(2*N+1)^2 + 32*(N+1)^2 + 49.
C = S + beta(L+Q+2*N+3)*908*(N+1)^6 + 4.
```

The singleton invocation costs at most C when a candidate exists. Disjoint flattening separately costs `4*flattened-block-count + 5*answer-pair-count + 1`, retaining empty and repeated blocks; its continuation adds the checker and four source operations. For m literal raw-parent candidates, `raw_parent_global_work` proves a bound of `(C+32*(N+1)^2+20*(N+1)+8)*(m+1)`. `raw_parent_setup_paid` proves that the actual sum of all per-occurrence setups is paid by the executed selection, including rejected duplicates. The polynomial is derived from source calls and is never a runtime argument or a desired whole-cost record.

Candidate size bounds are established before the parent invocation. `raw_parent_candidate_sizes` uses the actual generic recursive callee's returned partition of the unchanged target, without assuming the parent's acceptance. `fast_singleton_candidate_sizes` reuses the licensed fast ordinary callback's returned-payload theorem under its displayed proper-input and answer premises. Independently supplied malformed payloads also satisfy the local work theorems whenever their displayed size and storage caps hold. The represented raw/scheduler producer equations and word-width provenance remain explicit integration obligations.

Known-answer controls include q=8 for a two-leaf state, paying3 to obtain5, malformed empty-block rejection, disjoint flatten work23, first-candidate tie selection, and two setup charges for duplicated rejected candidates. The controls make no independent verification claim. Frozen packages and original failures were preserved; the collided pre-existing CallerSetup module was never compiled or changed. The attempted own source is retained, and the new module is BinaryCallerSetup.

Run `./bootloops-python research/rmaf/algorithm/universal233/ordinary_dispatch/forest_binary_caller_binding_20261016T092054Z/replay.py` for an exact same-lineage replay in a fresh result directory. The replay rebuilds only this package's source modules, retains the frozen dependencies, compares stored types/bodies/actual axiom records, and reruns the false, forbidden-axiom, and conversion controls. Fresh independent and novelty review remain open.
