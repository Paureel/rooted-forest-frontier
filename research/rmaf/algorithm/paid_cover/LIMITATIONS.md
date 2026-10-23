# Execution limits

The mathematical pseudocode uses finite source-edge enumeration for every
well-formed state, with explicit infeasibility and original-state fallback.
The research Python implementation imports recursive tree parsing and
restriction/shape routines from `pure_bridge/check_geometry.py`. It can
therefore hit the Python recursion limit on sufficiently deep trees.
Arbitrary-depth software support has not been implemented or tested.
Memory and runtime of exhaustive enumeration can also grow with n and q;
the delivered code is not a competitive FPT implementation.

The finite counterexample and control receipts concern only their actual
small trees. No conclusion about unrestricted runtime, complete graph
formalization, arbitrary-depth execution, or novelty follows from them.

This execution-limit note was added after `DELIVERY-MANIFEST.json` froze.
`DELIVERY-AMENDMENT-v2.json` preserves that original manifest and hashes this
additional note. No original scientific receipt or source was overwritten.
