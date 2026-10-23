# Numeric review protocol

The target and the charge-route README, WORK_PLAN, CONTROL_SPEC and
FROZEN_CONTROLS were read before this protocol. No proof or author checker
body has been read. The reviewer shares those contracts and fixtures with
the author; the evaluator implementation and comparison procedure are fresh.
Gatekeeper's guide was consulted: its AMFlow/fit interfaces do not implement
finite rooted-tree supports or list charges, so this review needs a one-off
exact evaluator.

Traverse each tree to list vertices and leaf addresses. Validate the index
list against support keys, nonempty leaf-bearing connected supports,
disjointness, leaf coverage and exact root owner. Calculate each side's live
indices from intersection with the leaf addresses, keeping indices distinct
regardless of equal labels. Trim addresses only after selecting live indices.
Calculate charges as sums of index indicators, then compare every expected
field recursively, with exact numeric equality and no tolerance.

Before proof inspection, require all eight positive fixtures and all eight
wrong-output clean twins to pass, all eight altered outputs to fail, all four
malformed inputs to fail for their own defect, and the raw leafless incursion
to remain a valid family outside the root-liveness premise. Empty-list charge
is exactly zero. An actual copied source with numeric comparisons disabled
must let the five numeric corruptions escape, and the outer run must reject
that copy. No result may be inferred from exit code alone.

Run the full battery with a 30-second subprocess limit, recording exact rows,
diagnostics, runtime and source hashes. The first run is the timing pilot;
no long computation or search is planned. Freeze sources and inputs by hash
before the initial execution and retain any failed attempts unchanged.
