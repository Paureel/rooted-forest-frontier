# Frozen geometric controls (before construction proofs)

Freeze date: 2026-10-14. Existing campaign controls were read before these
small Lean controls. These are exact definitional/kernel controls, not fresh
nonauthor verification and not full family acceptance.

* Singleton children have support only at their roots. Joint support is exactly
  root, 0, 1. Root, left leaf, right leaf must pass; address 00 must be absent.
* A left child support containing root and 01, with the needed stem 0,
  produces parent addresses root, 0, 00, 001; a singleton right adds 1.
  Address 001 must be present; 01 must be absent.
* Two actual false theorem files must fail under `by decide`: singleton joint
  excludes root; asymmetric joint includes 01. Each has the identical clean
  twin with the correct polarity in the positive file.
* Existing gapped support (root and 00 with missing 0) is not path convex;
  its negation theorem is an upstream supplied regression control.

Failure: any positive compile failure, a false theorem accepted, or negative
failure without `decide` false-proposition diagnostic. Controls run before
universal geometry proof compilation. No tolerances and no native_decide.

Expected answers were stated directly as address lists; they were not obtained
from the function under test. The Lean compiler/kernel and shared address/tree
semantics are common layers. These controls test the construction interface,
not independent truth of those shared semantics.
