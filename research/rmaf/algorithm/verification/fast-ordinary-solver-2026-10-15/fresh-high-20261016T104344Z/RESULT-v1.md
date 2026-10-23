# High-branch geometry reconstruction

The literal dichotomy remains OPEN. I obtained no counterexample and no universal proof of the final pendant refinement. The package contains universal Lean proofs for the endpoint and restriction steps, followed by an explicit unproved source-boundary proposition. None of these results establishes HighRule coverage.

## Proved components

`Geometry15.lean` proves `OwnHigh.cherry_distinct`: `DepthOne.proper T S = true` and `CoreGraph.CherryAt T p a b` imply `a ≠ b`. `CherryAt` alone permits equal labels; the equal-label control demonstrates this.

`Shared23.lean` proves `OwnHigh.agreement_singleton_or_shared`. For any raw agreement forest and a cherry of T, `[a]` belongs to the forest, `[b]` belongs to the forest, or one block contains both labels. Properness is unnecessary for this component. The proof reconstructs both endpoint embedding arguments, partition elimination, and pairwise embedding elimination from definitions.

`Restriction25.lean` proves `OwnHigh.agreement_source_cherry`. A shared endpoint block retains the cherry when T is restricted to that block. The unordered `sameShape` check transports the cherry, allowing either endpoint order, to the restriction of S.

`Boundary26.lean` proves `OwnHigh.refines_of_no_crossing`: if each block meeting a source pendant subtree lies wholly within that subtree, then every block lies in one pendant block or in the core block. The same file proves `OwnHigh.literal_consumer`, whose first premise is the explicitly unproved `OwnHigh.SourceBoundaryObligation`.

## Remaining statement

`SourceBoundaryObligation` quantifies over a source tree S, distinct labels a,b, a raw forest F, and a block P. Its premises require distinct source leaf labels, a valid source partition, pairwise disjoint source embeddings, membership of P in F, both endpoints in P, and a cherry with endpoints a,b in the restricted source tree. Its conclusion says that every forest block meeting any subtree in `cuts S a b` stays entirely within that subtree.

The exact Lean type is retained in `Boundary26.lean`, `Boundary26.log`, and the stored-body files. `literal_consumer` shows that this source-only statement suffices for the original target with exactly its frozen premises. I have not proved `SourceBoundaryObligation`. The stronger literal statement was not refuted, so no replacement by a narrower selected-high domain was attempted.

The mathematical reason to pursue the source statement is specific: the shared endpoint embedding should prevent other blocks from crossing each cut boundary, while the cherry in the restricted source should prevent the shared block itself from entering a pendant subtree. That sentence is a proposed proof route, not an established lemma.

## Executed evidence

The ten controls frozen in `CONTROLS-PIN-v1.md` pass kernel checking in `Controls13.lean`. They include identical cherries, either singleton endpoint, same-block and multiblock agreement forests, an equal-label cherry, improper input, and a shape disagreement. `refinesB_correct` proves that the finite Boolean refinement check has the literal `VertexGeometry.Refines` meaning.

All six deliberately false declarations in `Corruption27.lean` were rejected by `decide`: wrong pendant partition, omission of either singleton branch, swapped source, equal-label distinctness, and improper input accepted as proper. The full compiler messages remain in `Corruption27.log`. Supplemental controls in `SourceControls28.lean` check a raw agreement forest whose source cut list has length two; these controls were authored after the reduction and receive no independent acceptance credit.

`Audit32.lean` traverses stored types and proof bodies, including recursor rule expressions. Its graph has 1,174 declarations and retains 69 own producer bodies. No forbidden declaration, missing body, partial definition, or unsafe declaration occurs in that closure. Its axiom set is exactly `Quot.sound`, `propext`, and `Classical.choice`. A second run on a separate planted proof chain detects `OwnHigh.auditForbiddenMarker` two proof references away. `FINAL-VALIDATION-v2.json` separates the passing formal-component checks from the failed historical resource controls. `BODY-ARCHIVE-v3.json` indexes 29 lossless compressed chunks, each holding at most 4 MiB of uncompressed proof data.

## Primitive reuse

The proofs use the pinned program definitions and compiler-generated equation facts. Lean's imported simplifier also used `RestrictionBridge.root_not_prepend` and its generated simplification wrapper, from the pinned `GroupEmbedding` module. Their exact statements are `∀ s a, ¬ [] ∈ RMAF.prependSide s a` and the equivalent proposition equality to `False`. These are reused list facts and receive no independent reconstruction credit. Their stored statements, body references, module provenance, and transitive closure are retained in the dependency and reuse records. No safety, exchange, coverage, solver exactness, or global-minimum result was reached.

## Contacts and limits

The target was read and pinned before the own skeleton and initial contact ledger were written. Supporting Lean inspection used the staged definition excerpt and constrained names/types/definitions from pinned prebuilt objects. No full upstream program Lean source file or forbidden author proof body was opened; installed standard-library implementation sources were permitted supporting material. The large licensed manifest exposed author status metadata, and a filename-only launcher search incidentally listed unrelated review filenames. Neither supplied a mathematical premise. The final contact ledger records these incidents and the imported list-fact reuse.

Preliminary namespace probes failed through allocation errors, an incorrect use of `Name.getString!` on generated numeric names, and one 30-second timeout. A dynamic `FastSolve` import probe failed and measured 3,490,316,288 bytes of child peak RSS, exceeding the target's 3,072 MiB limit; it supplied no definition or proof output and is excluded from accepted evidence. I reduced imports to `Ordinary` and `ProperJobs`. The accepted proof runs and final audits remained below the memory limit; `Audit32` measured 1,851,768,832 bytes. macOS denied the earlier `/usr/bin/time -l` peak-memory query, so later runs used `getrusage` receipts.

The raw stored-body JSON exports were a separate resource failure: printing shared expressions as expression trees expanded one file to 110,919,620 bytes, above the raw and line caps. The files are preserved as failed exports. The version-3 archive splits their complete byte stream into bounded compressed chunks and verifies every chunk after decompression. Resharding repairs the delivery format; it does not erase the original cap violation. No claim of full resource-policy compliance is made for this arm.

No optimum oracle, author control program, solver execution, broad census, upstream source rebuild, or new engine was used. The workspace-wide `bootloops-check` suite was skipped because this work adds isolated problem proofs and the target prohibits a broad rebuild. Actual HighRule use-sites were not inspected. A separate interface review remains necessary before any component can support HighRule acceptance. There is no full solver, runtime, base, native execution, novelty, or replication claim.

I applied prose-lint in two passes to this report, first checking scope and numbers and then reading for clarity. The report's OPEN status follows the missing source-boundary proof; passing finite controls does not change it.
