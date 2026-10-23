# Fresh restriction review, phase 2

Scope: pinned family restriction/recovery interface only. Full G2, legal DP
states, graph correspondence, algorithm correctness and exponent claims excluded.

Main proof manifest SHA256:
75c6e470144991f06480a2cb03dd4e71367c4063c455051d91735d1bf96e2384

## Planned sections
- Input integrity and isolated source snapshot: pending.
- All 12 main modules and 5 false statements: read/review pending.
- Fresh Lean 4.35.0 dependency rebuild and axiom audit: pending.
- Five false arithmetic failures with clean same-import twins: pending.
- Actual exported-interface consumer: pending.
- NormalizedRestriction, RawIncursion, forged normalization: pending.
- Main REPORT prose/claim passes, twice: pending.
- Exact scoped verdict, evidence and remaining limits: pending.

Phase 1 bytes and all earlier pins are immutable. No charge-route source will
be read. No inherited oleans will be used. Fresh computations will be measured;
progress is compiled source/query/control receipts, never process liveness.

## Semantic review: definitions, geometry, constructed Family

Read RestrictionDefs.lean lines 1–25, RestrictionGeometry.lean lines 1–66,
and FamilyRestriction.lean lines 1–95. `OpenBranchLive` quantifies only an
actual boundary owner. `occupied_live` separates that owner from nonboundary
indices; the latter use a labelled leaf and cross-root convexity. The `restrict`
record supplies all Family fields and uses `selectIndex A.finite (Live A side)`;
its support and child-root boundary equations are explicit, with coverage
constructing the subtype leaf witness. No label equality is used to identify
indices. These claims still depend on the fresh kernel rebuild and source
audits below.
