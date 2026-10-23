# Retained assembly review attempts

No author source, old 45/377-file freeze, or pre-candidate mathematical
expectation changed. All positive author source modules passed their first
kernel build. The following are verifier inventory/instrument attempts.

1. The assembly certificate records two upstream stacks, with 17 repeated
   byte-identical module inputs. An initial assertion expected one input row
   per positive module and stopped before copying/building assembly. The
   corrected instrument verifies every repeated pin and compiled-source hash,
   retains equivalent source contacts, then follows the explicit 45-module
   positive order. It does not silently choose different source versions.

2. `isolated-assembly/FailedIncompleteAudit01.{lean,log}` and
   `isolated-completion/FailedIncompleteAudit01.{lean,log}` preserve initial
   audits importing only the final control module. Some independently built
   upstream fixture modules were not transitively imported. The Lean audit
   itself compiled, but the verifier correctly rejected expected origins with
   no records. Explicit imports of every positive source module produce the
   complete 2,117/2,491 inventories. No source theorem was repaired.

3. `FailedAuditInstrument01.py`,
   `isolated-completion/FailedOriginLedger01.lean`, and
   `CancelledOriginLedger01.json` retain a slow second-inventory design. It
   erased duplicates across the entire Lean/Std environment before filtering
   project modules, causing quadratic overhead. That own audit session was
   stopped with Ctrl-C (exit 130) before any ledger row was emitted. Process
   inspection by ps was unavailable in the sandbox; the existing exec-session
   interrupt sufficed, without escalation or action on an author process.
   The corrected ledger filters module origins first, then deduplicates only
   the 2,563 reviewed declarations. Its complete names/modules match the other
   inventory exactly. The cancelled attempt contributes no scientific evidence.

4. The frozen reference and actual author four-chain call orders differ.
   This is retained explicitly in the actual-readout receipt. Every named
   call's color/output/cut expectation matches, the exact actual concatenation
   is tested in its own order, and a new universal Lean proof establishes the
   multiplicity-preserving permutation. No reference order or author theorem
   was edited. Numeric base-four joint encoding matches exactly.

All fifteen explicit false proposition controls are intentional failures with
the required false-proposition diagnostic; each clean twin passes. Custom
axiom toys intentionally compile and are then rejected by the origin/axiom
gate, including unused private/public axioms. These are controls, not positive
source dependencies or unresolved mathematical failures.
