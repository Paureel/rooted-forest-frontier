# Repository framing review

This review ran in a fresh agent context using the referee-sim, prose-lint and
reading-contract protocols. It covers the new README, current-status,
reproducibility, large-files, research-map and coordination documentation;
AGENTS.md, autoresearch.md, CONTRIBUTING.md, CONTRIBUTORS.md, NOTICE,
CITATION.cff, task cards, issue/PR templates and CI configuration. Scripts were
read to check command promises. No research calculation, literature audit,
formal replay, source-by-source rights audit or full archive hash check was
performed by this reviewer; integration execution is a separate check.

## Read evidence

The source campaign specification is retained at research/rmaf/spec.json.
Its baseline field, line 8, says “this prior art blocks an unqualified novelty
claim.” Its acceptance list, line 9, requires full-text literature review,
complete correctness/termination and complexity proofs, formal audits, and
fresh semantic/independent verification. Algorithm TARGET.md:13 states:
“All three milestones are OPEN.” Imported progress/algorithm.json:5 says
remaining provider, cost, capacity and independent-correctness obligations
“still block the complete2.33 result”; line 7 reports
`"proved_improved_algorithms": 0`. These are retrieved source statuses,
not conclusions from new mathematical work.

PIN.md:7 defines ordinary unaugmented inputs, vertex-disjoint minimal
embeddings and separate empty-state treatment. The import summary,
docs/import/snapshot.json, declares a live file-by-file snapshot, source roots,
included-file counts, exclusions and hashes. Sample inclusion and omission
records were opened; completeness of every source path was not independently
reconstructed in this review.

The command audit read Makefile; activate.sh; the portable Python, Lean, Lake,
toolkit and dashboard launchers; scripts/bootstrap_toolkit.py;
scripts/check_repository.py; scripts/verify_small_instances.py; and the relevant
archived comparator and root-model audit. NOTICE:7–19 preserves third-party
exceptions. The two included BootLoops MIT notices retain their original
copyright line. No claim about a paper's legal redistribution rights is made.

## Audience and objection table

Severity describes the pre-fix framing risk. LOW includes objections already
answered clearly on the reader's path; MEDIUM identifies a clarification
needed before circulation. Correctness and novelty are assessed separately.

| Audience | Strongest standard objection | Axis | Answer and source locator | Severity | Fix or verdict |
| --- | --- | --- | --- | --- | --- |
| rMAF algorithm researchers | Does the title and target imply a complete unrestricted improved solver despite unresolved coverage and full costs? | Correctness | README opening states the complete bound is unproved; current-status opening preserves conditional/scoped status. TARGET.md:9–13 and progress/algorithm.json:5–7 support the boundary. | LOW | Already answered at the opening; retained. |
| rMAF algorithm researchers | Has the earlier O(2^q n) claim been resolved before calling 2.33 an advance? | Novelty | README opening claims no novelty; current-status “Source records” calls both benchmark and thesis claim source reports. spec.json:8 explicitly retains the prior-art obstruction. | LOW | Already answered; no record or priority claim added. |
| Phylogenetic practitioners | Does ordinary rMAF here silently add rho, impose acyclicity, or apply q=k−1 to the empty input? | Correctness | README “Problem and conventions”; spec.json:7; PIN.md:7 explicitly treats empty states separately. | MEDIUM | README now scopes q=k−1 to nonempty inputs and points out separate empty-state treatment. |
| Phylogenetic practitioners | Is a practical improvement over current production methods demonstrated? | Novelty | README describes a research goal and preserved candidates, with no speedup, benchmark win or deployment claim. current-status disclaims a current world-record determination. | LOW | Already answered by goal/status language; no performance claim inferred. |
| Formal verification readers | Does the optional Lean target prove graph semantics, all archived candidates, or the full exponent? | Correctness | Reproducibility “Scoped Lean check” names the root model and open obligations. research/rmaf/lean/audit.py's certificate scope and remaining-obligations list agree. | LOW | Already answered beside the command; retained. |
| Formal verification readers | Are scoped checked declarations presented as a newly established complete algorithm? | Novelty | README opening and final paragraph distinguish scoped formal checking from full acceptance; current-status opening says setup upgrades no scientific status. | LOW | Already answered; no mathematical novelty inferred from packaging. |
| Finite-check and verification researchers | Are both corpus engines rerun, are discovery cases called fresh certification, and does n=3..5 in the retained comparator output inflate coverage? | Correctness | Wrapper uses a preserved partition corpus and recomputes edge-cut optima. Archived compare_results.py:80,90 contains a fixed n=3..5 label. New wrapper writes actual-coverage.json and checks 9 ordered n3 pairs plus 225 ordered n4 pairs. | MEDIUM | README and reproducibility now identify the preserved partition results and fresh edge-cut computation; reproducibility explains the inherited label defect and actual-coverage sidecar. Comparator bytes preserved. |
| Finite-check and verification researchers | Is passing old finite data advertised as independent confirmation of a new algorithm? | Novelty | Reproducibility “Default finite checks” explicitly calls the work finite regression, excludes held-out certification, and limits the result to the preserved corpus. Wrapper lineage records shared definition/runtime and contacted cases. | LOW | Already answered; retained. |
| Reproducers and local dashboard users | Can a clone run the advertised commands with the stated dependencies, and do launchers actually create the historical automatic run history? | Correctness | Makefile requires make/POSIX shell. dashboard/server.py calls catalog() during import; dashboard/catalog.py:93–95 needs bootloops/tools/README.md. Portable launchers exec commands directly; historical dashboard/README.md describes instrumented launchers. | MEDIUM | README and reproducibility now name make/POSIX shell, require make toolkit for the dashboard, and disclose the portable launchers' lack of automatic stdout/exit/stage capture. |
| Reproducers and local dashboard users | Does a successful import check establish a new reproducibility or scientific-verification method? | Novelty | README “Local checks” limits success to finite and packaging checks; reproducibility distinguishes reused original evaluators from the new wrappers. | LOW | Already answered; no method novelty claimed. |
| Archive and research-integrity reviewers | Is this a complete atomic scientific release with all data and immutable historical commits? | Correctness | README “Archive coverage” and large-files “Snapshot limits” state active file-by-file copying, exclusions, no earlier Git commits and lack of cross-file consistency certification. snapshot.json states the export interval and policy. | LOW | Already answered prominently; full archive/source inventory comparison remains outside this framing review. |
| Archive and research-integrity reviewers | Does inclusion of old successful-looking notes select them as the current result or erase failed predecessors? | Novelty | current-status “Reading the archive” warns of superseded checkpoints and unchanged provisional assertions; selected-result.json selects no complete result. Contribution documents require predecessor credit and preserve failed work. | LOW | Already answered; inclusion conveys preservation rather than acceptance. |
| Attribution and reuse reviewers | Does Apache-2.0 purport to cover retrieved papers, companion protocols or all historical authorship? | Correctness | README “Attribution and license”, CONTRIBUTORS.md and NOTICE:7–19 retain third-party rights, MIT notices and source-specific attribution. | LOW | Prose boundary is clear. Source-by-source rights were not audited; the review makes no blanket rights conclusion. |
| Attribution and reuse reviewers | Is borrowed collaboration structure or AI assistance disguised as original research or independent human review? | Novelty | README credits CrocSwap/integer-mult-bounds and Codex; NOTICE:21–27 distinguishes structure inspiration, no copied research code/results, and AI assistance from independent human review. snapshot.json pins the inspiration source. | LOW | Disclosure is explicit; absence of copied external research was not independently audited against that external repository. |
| Contributors and general readers | Can CI or maintainer integration silently promote an incomplete result, or do collaboration files authorize unsolicited external actions? | Correctness | CONTRIBUTING.md separates CI from acceptance; AGENTS.md and coordination.md preserve scientific criteria and restrict external actions. PR/verification/task templates request exact scope, evidence, contacts and remaining hypotheses. | LOW | Already answered; no instruction/launcher conflict changes scientific acceptance. |
| Contributors and general readers | Is the task catalogue an announcement of new discoveries or an authoritative live list of unsolved work? | Novelty | autoresearch.md, coordination.md and task-catalog.json call the catalogue orientation and require current-source/coordination checks. | LOW | Already answered; no live-status or discovery claim inferred. |

## Opening-only and prose review

Read alone, the README opening states a research goal, marks the complete bound
unproved, and declines a theorem or novelty claim. No later caveat is needed to
reverse the opening's scientific status. A separate sentence-level pass checked
status words, parameter conventions, source attribution, measured-versus-goal
language, missing prerequisites and cross-document agreement. The edits above
were reread after the first pass. Ordinary software vocabulary was retained
where it describes actual software; scientific scope qualifications were not
removed for style.

## Applied edits and remaining verification

Only README.md and docs/reproducibility.md were changed by this reviewer,
alongside this new report. Imported research, results, progress, dashboard,
protocols, manifests and scripts were not edited. The exact fixes were:
nonempty-input parameter scope; explicit make/POSIX-shell prerequisites;
toolkit prerequisite for dashboard startup; preserved-partition/fresh-edge-cut
comparison provenance; actual-coverage sidecar and inherited comparator-label
disclosure; historical versus portable launcher-recording behavior.

No unresolved scientific overclaim was found in the reviewed new prose after
these fixes. The parent integration pass must run make check after incorporating
the documentation edits and inspect their diff as the second editor. Its test
receipts, rather than this report, establish whether commands executed and
checks passed. The full source archive, external literature and source-specific
rights remain outside this bounded packaging review.
