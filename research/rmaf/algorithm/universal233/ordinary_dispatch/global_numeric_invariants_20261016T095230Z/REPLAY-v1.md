# Replay in a new directory

Preserve this frozen directory and the completed dependency pool. Copy the thirteen owned .lean files named in FINAL-MANIFEST-v1.json, together with lean-toolchain, into a new directory. Set LEAN_PATH to that new directory followed by the exact dependency pool in DEPENDENCY-PINS-v2.json. From the new directory, invoke the workspace bootloops-lean with --memory=3072 and -o NEWDIR/Module.olean NEWDIR/Module.lean, in this order:

NumericPrecontrols, NumericLocal, NumericRule5, NumericStep, NumericReach, NumericSizes, NumericStateBounds, NumericEntries, NumericActualEntries, NumericSourceBinding, NumericOperands, NumericInterface, NumericControls.

Use an external 30-second timeout for each invocation and keep every log. No dependency is rebuilt. NumericFalseControls.lean and NumericConstructorFalseControls.lean are expected to fail; the final latter source has four mathematical errors, and no missing-name or syntax error. Source/object receipt binding is implemented in compile_v2.py. Its default output path belongs to this frozen directory, so reviewers should use its logic in their new directory rather than execute it here.

Full owned source/body/axiom evidence is indexed by author-audit-v4/certificate.json. The source extractor is reused from the completed licensed audit engine, with full proof text enabled. audit_v4.py retains the exact adapter and requires a new output directory for any replay. Independent verification requires a fresh author and separately written checks; replaying these author adapters does not confer independence.
