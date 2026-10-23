# Ordinary rooted MAF 2.33 - expert review packet

Read `PROOF.pdf` or its editable source `PROOF.md` first. The document plus the included electronic appendices is the self-contained submission. The PDF alone does not print thousands of lines of supporting Lean terms: those terms, all procedure bodies and exact dependency contexts are in this same packet. No original workstation checkout, chat transcript, cached compiled object or hosted service is needed to read the complete supplied argument.

The request is a correctness audit of an exact ordinary rooted binary MAF algorithm and its fully charged O*(2.33^k) mathematical log-cost RAM bound, k optimum components and cuts k-1. This is an internally accepted mathematical argument awaiting outside human review. It is not advertised as a wholly machine-checked runtime theorem, certified numeric executable, practical solver, or novel/best-known result. Verification limitations are prominent in the abstract, Section 11 and `verification/VERIFICATION-LIMITS.md`.

## Contents

- `PROOF.md`, `PROOF.pdf`: exact statement, assumptions, algorithm, proof assembly, cost algebra and review questions.
- `algorithm/`: complete frozen finite procedure bodies, representation/fee table, data and exact projection/entry amendments.
- `mathematics/`: all detailed mathematical operation, payload, guard, call-occurrence, decoder, scalar and width proofs used by the assembly. Historical OPEN labels in early component drafts are resolved by the later explicitly named addenda, not silently edited.
- `interfaces/`: full conditional theorem TYPES, graph constructors and computation views supplied to the final reviewers. Full proof terms are separately included under `formal/`.
- `formal/pools/`: project `.lean` sources, with separate provider pools preserved. `formal/CONTEXTS.json` and `BUILD-ORDER.json` identify exact imports and topological order for each main component context. `SOURCE-MAP.json` lists original relative paths and hashes. Standard Lean libraries are not vendored; `formal/lean-toolchain` pins Lean 4.35.0. No Mathlib dependency is expected by the supplied project import closure.
- `verification/`: final fresh-agent reports, contacts, controlled finite observations and selected original functional/SOURCE audit records. These are evidence with limitations, not additional axioms.
- `CERTIFICATION-ESTIMATES.md`: planning estimates for optional formal-runtime and executable certification; neither campaign is resumed.
- `ORIGINS.json`, `MANIFEST.json`, `CHECKSUMS.sha256`: original-to-portable file map, package file inventory and byte integrity. Original absolute paths inside immutable historical records are provenance locators, not runtime dependencies.
- `READING-MAP.md`: current portable destinations for historical release names and appendix aliases.

The author-side `prepare_packet.py` and `render_proof.py` are one-shot assembly/layout records. They are not proof checkers or necessary review dependencies, and the copy assembler expects the original local author checkout. The already-supplied sources/PDF are the review inputs; do not run the copy assembler to rebuild formal components.

## How to check the packet

From the extracted directory run `shasum -a 256 -c CHECKSUMS.sha256` (macOS) or `sha256sum -c CHECKSUMS.sha256` (Linux). A matching hash establishes byte identity only, not mathematical truth. The outer zip also has a separate SHA256 file.

The default review is read-only. There is no auto-run proof job, installation, network connection, external message, dashboard or monitor. Standard Lean 4.35.0 is needed only if a reviewer elects to rebuild formal components. Read `formal/REBUILD.md` before doing so. Such a future rebuild would not formalize the remaining mathematical prose automatically. No new full-corpus rebuild was run merely to assemble this packet; original receipts retain their original scope.

The small packet includes selected final evidence and its failure/contact qualifications, not every exploratory artifact from the full local project. Main proof dependencies are included; no claim is made that this is a complete laboratory-history archive. Please report any needed file or implicit premise that the manifest fails to supply.

All other research, certification campaigns and scheduled monitoring remain paused. This package was prepared locally for its owner to send; it has not been sent to anyone or published.
