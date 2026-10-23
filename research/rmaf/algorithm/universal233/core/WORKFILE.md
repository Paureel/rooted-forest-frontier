# Universal 2.33 source core workfile

Status: OPEN. Scope: concrete rooted graph/partition semantics for the colored-source cherry generator. X0 is a retained prerequisite, not a universal proof.

## Required claims

1. Homogeneous cherry coarsening covers every valid monochromatic source partition by refinement.
2. Unique-color group detachment preserves coverage.
3. At a mixed cherry, at least one pure child detachment preserves coverage.
4. Original-label lifts realize every emitted partition by exactly pieces minus one nonredundant original cuts, including root suppression.
5. Core mass is at most c^(1-r) for c >= 2 and every emitted cost is at least r-1.
6. Budget-pruned generation accounts for all prefixes and costs O*(2^q).

## Evidence and provenance

- Target: `../../ALGORITHM-233-UNIVERSAL-TARGET.md` and `../../NEXT-MULTICOLOR-CORE-PIN.md`.
- X0: `../x0/multicolor/REPORT.md`; do not repeat the census or read its large raw receipt.
- Prototype contact, if read, is DEVELOPMENT only.
- No optimum oracle is permitted in production.
- Lean acceptance requires source-bound compilation, complete axiom audit and a rejected false-proposition control; no sorry, admit, custom axioms, or native_decide.

## Running journal

- Initial target read; obligation skeleton recorded before proof work.

## First unresolved consuming claim

Not isolated yet. No completed theorem is claimed.

- Consulted BootLoops tools index and theorem/graph capability entries; no general package implements this concrete source generator. Reuse the existing `RMAF.Tree` vocabulary but develop the local graph lemmas here as problem-specific proof code.
- Read only definition/proved vocabulary in `research/rmaf/lean/RMAF.lean`, `bridge_review/lean/GraphRegion.lean`, and `bridge_review/leastness/address_semantics/TreeAddresses.lean`; no pending sibling or safe-cover theorem used. All viewed material is DEVELOPMENT contact.
- Read `x0/multicolor/prototype.py` as DEVELOPMENT contact; no claim of independence from that prototype. X0 report read; raw receipt and census not rerun.
- First Lean pilot: `Smoke.lean`, approximately 3.09 wall seconds including dashboard/compiler startup. Known arithmetic example compiled; diagnostic `#check` probes intentionally reported several unavailable API names. No scientific acceptance follows from this probe.
- Planned Lean jobs are small local proof compilations, not an unmeasured large calculation. Retain wall timings and compiler logs per compilation.

### Kernel-checked local graph results (author compilation, not fresh verification)

- `CoreGraph.lean` defines the actual rooted source graph using `RMAF.Tree`, executable address lookup, parent/child adjacency, and finite walks. Source partitions have ordinary connected, vertex-disjoint supports with exact leaf membership; no coverage or contraction conclusion is a structure field.
- `mixed_cherry_singleton`: different cherry colors force at least one current leaf to be the only leaf in its partition block. Proof: a nontrivial leaf-to-terminal walk visits the actual parent; two nonsingleton blocks would overlap there.
- `unique_color_singleton`: a color used at only one current leaf forces that partition block to be a singleton.
- `CherryCoarsening.lean` explicitly constructs a source-graph partition coarsening joining homogeneous cherry leaves, preserving monochromaticity and the refinement direction `P refines Q`. The parent can be free, in a cherry block, or in a third block. A generic walk theorem removes a vertex with at most one support neighbor from third-block excursions.
- Initial author compiles succeeded. Current local theorem audits contain only standard Lean axioms (`propext`, `Quot.sound`, and for classical singleton case splits `Classical.choice`). No custom axiom or unresolved proof is accepted.
- The source-support model is a direct actual graph semantics. Equivalence to the existing Boolean `RMAF.pairwiseEmbeddings` checker and grouped-tree contraction/suppression maps are not yet proved here. Thus no full generator coverage theorem is claimed.

### Executable candidate and bounded prefix work

- `CoreProgram.lean` now implements original-address groups, homogeneous normalization, unique-color choice, both mixed-cherry choices, group deletion with unary/root suppression, original-address cut records, explicit refusal paths and budget-pruned recursion. It never queries an optimum or enumerates source partitions.
- The literal control sheet `PROGRAM-CONTROLS.md` was written before candidate execution. Nine kernel-reduced controls pass, including both crossed-quartet cores, insufficient budget, homogeneous coarsening, distinct/three colors, root/singleton, and duplicate-label refusal.
- Early control equality failures were representation-order mismatches: mathematical partitions are unordered. Added explicit structural insertion sorting in the control display only. The target memberships and charges were preserved. Early `mergeSort` controls could not reduce in the kernel, so the display sorting was replaced by structural recursion; no `native_decide` was used.
- Author-compiled universal program bounds: `visited+1 <= 2^(q+1)`, `childAttempts <= 2*visited`, and `visited+childAttempts+3 <= 3*2^(q+1)`. Failed/root/duplicate/pruned child attempts are included. This is the combinatorial prefix-work bound; a full per-node polynomial size/cost proof remains open.
- `CoreInvariants.lean` proves normalization preserves the ordered original-label payload and group purity. Every emitted cut *record* is nonroot and pairwise distinct, and recorded pieces equal recorded cuts plus one. These statements do not establish actual original-edge realization or nonredundancy in the cut graph.
- Current CoreProgram and CoreInvariants successful audits use only standard `propext`/`Quot.sound`. Rejected author proof attempts are retained in `build/*-first.log`, etc.; the final replay will audit current sources afresh.

### Source-bound acceptance evidence

- `./bootloops-lake -d research/rmaf/algorithm/universal233/core build` completed successfully (12 jobs), 10.12 measured wall seconds. Full log: `build/lake-build-first.log`.
- `replay.sh` completed from copied current source at `replay/20261015T063857Z/`, with SHA-256 hashes and source comparisons. Its retained `VERDICT.txt` and `audit-check.log` state:
  - `PASS: source-bound compilation, 112 complete axiom audits, 9 positive controls, 3 rejected false controls`
  - `PASS: 112 / 112 declarations; only standard Lean axioms ['Classical.choice', 'Quot.sound', 'propext']`
- All three negative control compiler logs contain the specific phrase `is false`; an infrastructure failure is not accepted as a false-control catch.
- These are author-executed compiler/control receipts. No nonauthor verification or complete core closure is claimed.

### First unresolved claim

- Exact statements and consuming lines recorded in `FIRST-GAP.md`.
- External interface: existing `partitionCheck` and `pairwiseEmbeddings` source checks to the constructed connected-support `SourcePartition` representation.
- First internal graph gap: `CoreProgram.lean:110`, transporting homogeneous coarsening through actual grouped-tree normalization and original-label contraction maps. `erase`/suppression and original-cut graph realization follow as separate gaps.
- Strongest proved route: local original-graph cherry surgery plus an executable budget-total candidate and bounded prefix count. Proposed different continuation keeps full original cut connectivity and proves suppressed skeletons only as representations.

### Report review

- Acceptance-gate and planted-truth checked; literal controls and compiler rejections retained. No digit/fit claim applies here.
- Report drafting used reading-contract locators and two author prose checks: first for overstatement of complete coverage/cut realization/runtime, then a separate sentence-level clarity pass. The report scopes all proved quantities and unproved interfaces.
- Fresh-context referee simulation remains for the parent's independent verification phase; assignment forbids this arm from spawning further agents. Parent notified. No outward VERIFIED-CLOSED label is used.
