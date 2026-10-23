# Family adversary work skeleton

Started 2026-10-14 after reading `FAMILY-TARGET.md`, before reading any new author family model, code, or proof.

## Scope
Independently check the stated labelled finite-tree family normal form, source-disjoint trimming, and treatment of leafless open child fragments. Preserve exact witnesses and limit finite testing to NO-FIRE evidence.

## Sequence
1. Read the frozen specification, accepted connected-region interface, and applicable protocols.
2. Freeze positive and corrupted controls before implementing the checker.
3. Implement and run a tiny exact checker using `./bootloops-python`.
4. Report counterexample or missing hypotheses and explicit NO-FIRE scope before author proof construction.

## Independence firewall
Do not read new author family sources or proof candidates. Owned files: this directory and dedicated triple-family-adversary receipts only.

## Source extraction, 2026-10-14
Read `FAMILY-TARGET.md` and `PROOF.md` (the existing debt specification). In `PROOF.md`, “An open region is the region that contains v and may extend through the parent edge” pins the root-membership convention; this resolves the initial ambiguity in the short target. The specification also says “We may thus require every open region to have a nonempty label set below its boundary.” These are required hypotheses in the checker; removing either gets a separate hostile control, not an in-regime counterexample.

Protocol decisions: this is Regime 1 / X0, not a closure attempt. Expected outputs are manually constructed finite sets, frozen before checker code. Regression examples cannot become holdout evidence. New controls burn into construction on first use and cannot certify a later author implementation. Runtime is unknown until a fixed-case pilot executes; no census expansion is planned. Toolkit capability index and roster were searched for a finite tree family/support checker; the general graph-related packages concern Feynman graph topology or integration, not rooted-tree region families, so this checker is a problem-local, one-shot instrument.

Accepted `ConnectedRegions.lean` was read. Its `gappedRegion` is exactly `{[], [false,false]}` (definition and final two theorems); it is LCA-closed and fails path convexity at `[false]`. Its `rooted_child_contains_root` and `rooted_region_decomposition` require root membership explicitly. No new family model, implementation, or proof has been opened.

## Controls and timing, frozen v1
`controls-v1.json` and its SHA256 were written before `check_family.py`. The one-shot checker uses explicit graph BFS paths; no author family implementation is imported or opened. The first execution used `./bootloops-python` with `--controls-only` and retained `results/triple-family-adversary-pilot.json`.

Verbatim pilot summary:
```
{"verdict": "CONTROLS-PASS", "positive_passes": 11, "corruptions_caught": 6, "elapsed_seconds": 0.0012202920006529894}
```
The fixed controls run the same trim/restriction/assembly code used by probes. The next run has at most 673 candidate supports across the five fixed trees (1 + 7 + 31 + 127 + 511); support generation is bounded before launch. The measured 11-family control battery takes 0.00123 seconds on this runtime; a linear projection is below one second even if every candidate is admitted, with startup overhead excluded. This projection is only a scheduling estimate, and the next receipt records measured elapsed time. No larger census is authorized or planned. Real progress is the number of admissible families with completed exact invariants in the receipt.

## Executed X0 result
Verbatim full-run summary:
```
{"verdict": "NO-FIRE", "positive_passes": 11, "corruptions_caught": 6, "elapsed_seconds": 0.015003124999566353}
{"discarded_raw_fragments": 21, "families": 119, "per_tree": {"balanced": 31, "cherry": 5, "deep": 68, "singleton": 1, "triple": 14}, "supports_considered": 677, "transition_counts": {"extend_0": 26, "extend_1": 18, "join": 37, "leaf": 1, "unused": 37}}
```
The prior timing note's handwritten total “673” was an arithmetic typo: its unchanged summands total 677, as the executed loop also counted. The fixture scope and checker did not change. The estimate stayed below one second either way.

Sent the exact NO-FIRE scope and necessary state hypotheses to the parent before author construction was authorized. Added a separate post-run hypothesis illustration receipt; it is explicitly not a new acceptance fixture. Acceptance-gate read before final reporting: this arm makes no CLOSED/VERIFIED-CLOSED claim. The report gives exact counts and catches, with fresh-author and formal checks left explicit.

Prose review: checked the report twice for claims versus receipts, source locators, arithmetic totals, context needed for standalone reading, and misleading claims of independence or universal proof. The parent/fresh reviewer remains the separate final reader. No source text outside the assigned adversary directory was modified.
