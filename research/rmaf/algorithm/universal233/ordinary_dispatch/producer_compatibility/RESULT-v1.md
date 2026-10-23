# Actual producer-compatibility controls

The Lean importer rejected same-name ordinary definitions from distinct
modules in both conflicting-value import orders. It also rejected the
equal-value twin import. No contradiction module compiled. These measured
outcomes are recorded in IMPORT-BEHAVIOR-v1.json; the pre-test pin described
kernel behavior as unknown. Equal-value compatibility in that pin referred
to the planned audit comparison, not successful joint module import.

The separately dumped actual definition producers distinguish the intended
cases: LeftValue/TwinValue have the same type and body and pass the new
comparison; LeftValue/RightValue are rejected in both orders because their
actual bodies differ. All three producer controls pass their expectations.
COMPATIBILITY-CONTROLS-v1.json retains the actual rows and the exact completed
author audit contact. This is instrument development, not independent review.

The gate allows different theorem proof bodies only when their propositions
and kinds match; the axiom/provenance gate remains separately required. It
requires exact type and body equality for duplicate definition/opaque values.
It conservatively refuses other duplicate nonproof metadata. Expression-text
equality is sufficient here; unequal text is refused even if values might be
definitionally equal. This may reject a usable pool and cannot silently accept
an unequal body. It does not claim to compare arbitrary compiler metadata.

The first control runner had a wrong repository-parent index and failed to
locate the completed audit before executing a producer audit. The corrected
runner and detector were pinned before their first successful application.
Original import logs, initial control pin and source fixtures remain retained.
No scientific frozen file was edited and no scientific pool was audited by
this small control experiment.
