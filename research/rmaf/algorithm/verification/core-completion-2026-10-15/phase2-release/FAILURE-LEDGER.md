# Retained review failures

All items are verifier implementation/audit attempts. No frozen author source
or pre-contact expected value changed. Positive source rebuilds succeeded on
their first kernel execution; the failures below do not describe failed author
theorems. Author and pre-contact hash checks are separate retained receipts.

1. Startup source certificate key was initially read as `hashes`; its actual
   key is `input_hashes`. This KeyError occurred before any source build.
   The corrected source-key lookup is explicit in `rebuild.py`. No source or
   build evidence was produced by that failed startup.
2. `isolated-source/FailedReadout01.{lean,log}`: list `getElem!` required an
   unavailable `Inhabited Output`. The new readout uses an explicit getD default;
   fixture output lengths/order are independently checked, so the default
   cannot mask a missing fixture output. The original partial readout is kept.
3. `isolated-source/FailedCleanTwins01.{lean,log}`: default `decide` did not
   unfold Rat division/powers far enough. `KernelTwins` and the final positive
   twins use `decide +kernel`, which checks reductions in the Lean kernel and
   adds no native-decide axiom. No native_decide is used.
4. `joint-copy/FailedConsumer01.{lean,log}`: the final c=233/100 lower-bound
   premise had the same rational reduction issue. Its replacement is exactly
   `by decide +kernel`; hypotheses and conclusions are unchanged. The failed
   compile record remains in the joint receipt, before the passing record.
5. `joint-copy/FailedJointAudit01.{lean,log}`: the initial final audit imported
   only the consumer; its transitive imports did not include the two fixture
   modules Controls/CutControls. It correctly rejected missing module origins.
   Explicit imports of those already rebuilt positive fixture modules give
   the complete 38-module inventory.
6. The first strict cross-package origin reconciliation rejected
   `(Entrypoint, Universal233.CoreProgram.generate.eq_1)` because the joint
   origin is InitialCoverage. The generated declaration is present in both
   isolated stacks with different lazy-generation origins. All three raw Expr
   types and proof bodies were compared and match exactly; this sole adoption
   is now explicit and independently tested. The final receipt contains the
   adopted origin and the fingerprint. No theorem body was altered.
7. `joint-copy/FailedPrintAxioms01.{lean,log}`: the mutable theorem counter lacked
   an explicit Nat type and was inferred as MessageData. Adding `: Nat` fixes
   the printer; its final log records all 1,154 theorem `#print axioms` outputs.
8. **Receipt correction:** `...-rejections-v1.json` incorrectly labels
   `FalseOmittedMass2` and `FalseOmittedMass233` as explicit false-proposition
   rejections. Their unchanged logs actually say reduction got stuck. The
   diagnostic validator was too weak because it searched for `false`, also
   present in “true or false”. These two attempts are inconclusive, are not
   counted, and remain at their original paths/hashes. V2 supersedes this
   classification and requires an explicit “proved that the proposition” /
   “is false” diagnostic with no reduction-stuck message.
9. `isolated-source/FalseOmittedMass2V2.{lean,log}`: a direct `change` from Rat
   division to mkRat failed definitional equality at tactic transparency. It
   is not counted. The V3 modules use separately kernel-certified exact mass
   and fraction identities, then ordinary `decide` rejects the explicit wrong
   mkRat equality. Both rational negative controls now have the required
   false-proposition diagnostic. `...-rejections-v2.json` binds those final
   controls and retains the old inconclusive records. `RatFalsePilot` is a
   deliberately false small ground-rational pilot, not an acceptance failure.

The v1 rejection harness is historical. The final authoritative correction
instrument is `correct_mass_controls.py`, and the authoritative rejection
receipt is `algorithm-core-completion-fresh-review-rejections-v2.json`.
