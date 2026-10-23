# Failure ledger (append-only)

Prerelease graph pilot and hand controls: no unexpected failures. All 14
deliberate corruptions were caught alongside passing clean twins; exact
records remain in graph-controls-v1.json. These are successful detector
calibrations, not candidate failures.

Operational limitation: lean and lake are absent from PATH. Root was asked
only for the runtime/API-documentation path. No candidate contact occurred.
Producer control execution and READY freeze remain pending.

Prerelease barrier incident: a coordination inventory exposed author/peer
final-answer summaries after all graph controls had completed. This weakens
strict no-result-summary-contact freshness from that point. No linked
candidate or peer source was opened, no author/peer was contacted, and no
summary assertion enters the evidence. Root was notified; exact release is
still required. This incident is preserved, not repaired or erased.

Lean API pilot v1: FAIL in 6.225006125 seconds under a 60-second timeout.
Three queried API names do not exist in Lean 4.35.0: Expr.fold,
Name.isPrivate, KVMap.toList. The runtime did confirm stored ConstantInfo
type/value access (with allowOpaque), ConstMap, module-index lookup, and
JSON compression. Receipt and original probe remain intact. This is an
instrument-construction failure before real candidate contact, not a
scientific candidate failure. Next version will use explicit constructor
recursion and actual runtime structure fields.

Lean API pilot v3: FAIL in 0.646253959 seconds: Syntax/Level/BinderInfo/
DataValue/SourceInfo lack ToJson instances. Their native constructor
interfaces were retained. The recorder uses explicit tagged encodings for
names, levels and expression constructors; Syntax-valued metadata refuses
instead of silently dropping information.

Producer compile pilot v1: FAIL in 0.788460667 seconds: missing explicit
ExprStructEq key type, absent Repr ReducibilityHints instance, and reserved
parser token `prefix`. Original source/receipt retained; v2 fixes those
construction errors without changing scientific expectations.

Producer full-control run v1: FAIL in 1.975666 seconds after seven commands.
Lean refused the A-then-B import at PlantCollision.shared before the recorder
could run. This is the intended collision being caught earlier by Lean, but
the original driver required successful combined imports and therefore
failed. Preserve original driver/receipt. Version 2 records both order
refusals as expected controls and independently records A/B producers in
separate fresh environments before comparing their stored bodies. A new
transitive body-only chain and structural-DAG calibration are prerelease
instrument tests; no candidate has been read or released.

Producer full-control run v2: FAIL in 3.00044325 seconds after eight commands.
Both separate-environment records were produced correctly, but the driver's
synthetic numeral extractor expected the DAG root itself to be a Nat
literal. Lean stores these source numerals as OfNat applications. The full
DAGs correctly retain distinct literal payloads 7 and 11. Version 3's
calibration-only extractor reads that unique stored literal; it is not
used as a general evaluator or to change expected planted values. Original
driver and failed receipt remain intact.
