# Common-split source review readiness

Status: READY for root review of this prerelease preparation. No candidate source, proof, program, control or receipt body has been contacted. This is not source-theorem acceptance and does not authorize self-release. The exact root RELEASE remains required before candidate work.

The detector controls and postrelease plan are prepared and locally executed. The future source review will require an actual constructed global `IsMinimum` witness and a lower bound against every original AF, derived from four true witnessed LOCAL minima. A formula that already assumes a global minimum is weaker. Even a verified graph theorem does not implement a caller that computes those four minima.

## Detector and executed controls

`ProducerAudit.lean` reads each requested producer's stored ModuleData arrays before name resolution. It streams every raw occurrence with physical part/index, actual ConstantInfo kind/type/body/recursor rules, structured names/universes/metadata, full import flags/order, direct dependencies, axiom/unsafe/partial/missing closure and resolved origin separately. `check_controls.py` tests small fabricated rows and exact mutations. `index_receipt.py` uses a sequential32-MiB row cap and compact SQLite hashes/keys, keeping full bodies on disk. Candidate work will not load a giant raw-body map.

All fabricated scientific producers import only Std; the detector imports installed Lean as infrastructure. Twelve control audit compositions cover13 producers and54 distinct stored occurrences (103 rows when repeated producers across compositions are included). These are inventory counts, not percentages of theorem acceptance. Four clean compositions pass; eight hostile compositions reject. Two separate compiler diagnostics reject a genuine False proof attempt and unsafe proof use.

| Control | Raw occurrences in composition | Result |
|---|---:|---|
|CleanBase + TrueDiagnostic|22|clean|
|CleanBase + CleanTwin|23|clean, two stored shared occurrences / one resolved name|
|CleanBase + CoalescedBad|23|reject same-name/same-type stored custom axiom|
|AxiomBad|3|reject unused and private False axioms; false theorem closure recorded|
|UnsafeBad|1|reject unused unsafe declaration|
|SorryBad|1|reject sorryAx|
|PartsClean|7|clean; four raw theorem views matched to same-producer private proofs|
|PartsBad|4|reject unused private False axiom|
|PartsClean + PartsCoalescedBad|13|reject hostile producer's axiom despite clean resolved theorem|
|AdmitBad|1|reject sorryAx|
|NativeBad|2|reject actual generated native-decide axiom|
|AllowedAxioms|3|clean; exact closures propext / Classical.choice / Quot.sound|

The native control's actual generated custom axiom is `TrustControl.nativeTrue._native.native_decide.ax_1_1`; both its direct occurrence and the theorem's dependency closure reject. This supplies an actual generated-axiom control rather than a merely generated-looking name. Clean private declarations and generated inductive constructors/recursors are also inspected. The unsafe-proof-use diagnostic fails in the kernel with its unsafe declaration named explicitly. The false-proposition diagnostic fails with the True/False mismatch; its matching true theorem passes.

The exact comparator caught23 deliberate adaptations: missing/duplicate occurrence, kind/type/body/name/levels/recursor/binder changes, altered import and import modifier, stored producer/resolved origin, source/olean bytes, unsupported expression tag and missing/altered/wrong-producer multipart proof evidence. The compact index separately matched all12 control classifications and caught nine integrity plants. The synthetic expression codec distinguishes20 roots, covers all12 Expr constructors via13 tags, and round-trips exact name/level/binder/literal/metadata/syntax/source-info content. Results are retained in the v7, v8, v9 and index JSON/log files.

Only propext, Classical.choice and Quot.sound are allowed in inspected dependency closures. Direct custom scientific axioms, unused/private/coalesced/generated occurrences, sorry/admit/native-decide dependencies, unsafe/partial scientific declarations and missing attribution reject. Compiler-only extraConstNames are separately inventoried; ten such names occur in CleanBase's metadata. Their bodies are not claimed inspected. Installed standard-library binaries are pinned trusted inputs rather than rebuilt here.

## Retained repairs

Every unintended failure remains in `FAILURES.jsonl`, with failed sources and logs. The initial detector compile failed on Lean API/elaboration details; the second failed on nested match-return elaboration. Both were repaired without changing scientific expected values. Default escaped Name display did not plant a display collision, so the later synthetic control uses unescaped display while preserving distinct structural names. Infrastructure path probes and a rejected patch are recorded.

The multipart clean control exposed a more substantial false positive: Lean exports theorem signatures as axiom views in public/server parts and stores proof bodies in the final private part. The v4 gate rejected those views. `PartsClean-v5-failed-gate.json`, the original rows/code, and E004 retain that failure. Installed Lean Environment.lean lines2248–2284 documents this transformation.

Schema producer-dag-v2 preserves every raw occurrence. A view is qualified only by a later actual theorem occurrence in that SAME producer's final private part, with exact structural name/type/universes, safe flag, singleton mutual-theorem membership and body evidence. The Python gate/index compares that proposed witness to the actual stored occurrence. Another producer's theorem, including the resolved environment's clean theorem, cannot qualify it. Missing/changed proof evidence rejects. The multipart hostile twin demonstrates this distinction. `REPRESENTATION-AMENDMENT-v6.md` and subsequent import supplement retain the scope change transparently; no earlier representation or result was overwritten.

## Timing and provenance

The tiny known-answer compile pilot preceded expansion. Repaired detector compilation took about0.9 seconds; stored dump pilots took about1.3 seconds. Numerical projections were written before subsequent bounded controls. Every compiler/dump command had a30-second timeout; the longest of58 recorded commands took1.4440662499982864 seconds. The compact-index controls took about0.6 seconds per receipt; the largest lossless row was6,158 bytes. These timings apply to fabricated controls; the released scientific package requires its own bounded build pilot.

`SOURCE-CONTACTS.json` pins30 allowed source/infrastructure contacts. Installed Lean source ranges used for the detector are listed there. No author/other-reviewer implementation, live proof, or child was contacted. Exact source/olean and trusted standard-part pins are retained in control results and the module maps. Cached Expr/Level bitfields and physical memory sharing are excluded from the structural representation; original olean bytes are independently hashed. Detector pointer memoization is infrastructure over retained raw objects and supports no unsafe scientific-proof claim.

The proposed source map is explicit in `POSTRELEASE-PLAN.md`: root-released byte manifest, one-to-one logical module/source/cold-olean registry, import parsing and full modifier/order comparison, isolated topological rebuild of all scientific sources without copied scientific oleans, actual Lean path resolution, every stored producer occurrence, same-producer view qualification, closure/origin inspection and compact disk index. Source options that bypass kernel checking must be rejected. Installed standard-library pins are trusted rather than rebuilt. Unavailable bodies, unresolved origins, oversize rows or unsupported constructs remain unaccepted scope gaps.

## Own X0 reuse and boundary

The old X0 manifest SHA256 is `71d7f7a05f46719b00429de09f49854ded115326429ff373bae158cd089a3b64`. All58 members were rechecked unchanged. `OWN-X0-REUSE-v1.json` binds exactly its six literal controls and eighteen label/order variants for future actual compiled candidate readouts. The old hand fixtures are already burned; its finite oracle and cut replay share Graph. This same lineage receives zero additional mathematical replication credit. No census was rerun or extended.

After exact root RELEASE, the reviewer must inspect the complete mathematical chain and every actual consumer premise, then adapt real released interfaces to the frozen literal controls. Missing runtime/minimum readouts stay untested; the old Python oracle's values cannot be substituted as candidate output. Representative invariance has only finite evidence until a source theorem proves it. The four missing finite joint buckets cannot be assumed impossible.

A graph theorem from four supplied true local minima leaves the future caller responsible for computing those minima, actual marked-instance/callback implementation, source Rule5.3.1 applicability and outside minimum, bounded algorithms and paid capped queries, executable forest/output-list reconstruction, state validity, strict progress, mutual recursion/termination and recurrence accounting. No polynomial extraction, free oracle, compiled-machine, global runtime/base, novelty or main-problem VERIFIED-CLOSED claim follows. All3main/global runtime/base/novelty remain OPEN.
