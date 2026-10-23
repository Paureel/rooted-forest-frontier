# Review records

The source-only isolated builds are in `isolated-review-v1/g` and
`isolated-review-v1/e`. `review_replay.py` created those empty directories,
verified release hashes, copied only .lean sources, and compiled through the
workspace `bootloops-lean` launcher with LEAN_PATH set to the relevant directory.
The driver refuses to overwrite an existing build. To repeat manually, copy
the sealed .lean sources into a new empty directory and compile in the module
orders retained in the JSON run records. Intentional false controls must fail;
they are excluded from accepted proof imports.

The joint directory contains the unchanged common and E source bodies plus
unchanged Selector. `Interface.lean` imports Selector and SourceEdge directly,
so neither author's Controls module is renamed or mixed with the other. The
six review interface theorems and their exact printed signatures are retained
in Interface.log. JointAudit lists all 961 actual originating declarations.

ActualReadout and the four Fixture sources emit JSON from the actual compiled
definitions. `actual_readout.py` compares those values to the independent
pre-candidate Python source in frozen-readiness-v1. Every emitted value remains
in the Fixture logs and Fixture-actual JSON files. The input partition literals
come from that own frozen enumerator, not an author/referee/X0 implementation.

The first ActualReadout failed elaboration because the length comparison had
type Prop while ToJson requires a serializable value. The failed source and
log are in `failed-instruments/actual-readout-v1`; its failed receipt is
`results/algorithm-pair-case-fresh-review-actual-v1.json`. The corrected source
uses decide to obtain a Bool. All four fixture sources then compiled and all
comparisons passed in actual-v2. This correction changed only result encoding.
The unchanged expected outcomes and original proof bodies remain hash-bound.

The eight supplemental corrupted-readout controls test the exact retained
verify_tree function extracted from actual_readout.py. A clean twin passes;
missing/duplicate cases, a spurious original address, altered region count,
missing or false selector result, and reversed original edge are all rejected.
They were added after release and are labelled supplemental throughout.

The release integrity receipt explicitly compares the two generated E audit
variants with their declared derivations. Each changes only one import and
one origin-inventory name; their origin descriptors are prose, not file paths.
The scientific source copies remain identical. The joint origin change for
VertexGeometry.Prefix.eq_1 is separately documented in the semantic report.

The original frozen-readiness seal was rechecked after all work. The final
sealed review copy includes proof sources, all audit/readout logs, exact result
records, failed attempts, and manifests. It deliberately omits compiled oleans
so future replay starts from retained source. Only the pinned local Lean kernel
and its standard library are shared by the formal replay and the authors.
