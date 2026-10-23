# Source detector controls v1 — pinned before final candidate audit

2026-10-15. These are fresh Std-only producer fixtures, isolated from candidate
imports. The completed rule5_local audit generator/parser is a DEVELOPMENT
contact, wrapped without modifying its frozen bytes. No independent reviewer
credit is claimed. Both import orders are mandatory.

- CleanA and CleanB each store the same name and exact True theorem type;
  CleanB also stores its own clean arithmetic theorem. Both stored occurrences
  must be recorded in A/B and B/A import orders, despite coalescence.
- Hostile substitutes a custom axiom at that same name/type, and also stores
  its own clean theorem. A/Hostile and Hostile/A must both be rejected for
  the direct producer axiom, regardless of resolved name attribution.
- A separate private unused False axiom plus own clean declaration must be
  rejected; a separate unused public axiom must also be rejected.
- Std True arithmetic must compile; its wrong-answer twin must fail.
- Candidate false-saving and wrong cost3→cost2 Lean claims must each fail.
- Missing/duplicate producer occurrence, wrong local module path, wrong source
  hash, and adapted-source byte mutation must each fail beside the clean twin.

Producer receipts record actual ConstantInfo kind, type, body, references,
axiom closure and stored producer separately from resolved origin. All rows
from every scientific producer must be present once. Standard axiom whitelist:
Classical.choice, propext, Quot.sound only. Source/byte correspondence is
conditional on these pinned adaptations and this executed Lean toolchain.
