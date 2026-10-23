# Independent edge-cut evaluator

This problem-local instrument computes ordinary rooted MAF optima for small
binary trees by enumerating every edge subset in each tree, removing leafless
components, suppressing unary vertices, and intersecting canonical forests.
It uses the shared no-rho convention and counts nonempty leaf components.

Reach for it to cross-check the campaign's structurally different leaf-partition
evaluator or to inspect an exact counterexample. It is exponential in the number
of leaves and is not the requested faster FPT algorithm.

Outputs are exact integer component counts, a canonical component topology
list, and two cut-bitmask witnesses. Vertex and edge indices are allocated in
preorder on each input. Any mismatch, malformed tree, or unequal label set
raises an exception. A finite pass cannot prove a proposed rule for all inputs.

Before using its results, retain the frozen hand-control fixture, execute all
controls and the deliberately wrong comparator pair, record the source hash,
and compare with a separate evaluator. The journal records when discovery
results were first accessed; subsequent comparisons do not become held-out
certification merely because the two programs agree.

Run the pilot with:

```sh
./bootloops-python research/rmaf/verification/edge_cut.py --max-n 4
```

The implementation and fixture are independent of the campaign's oracle source.
Shared layers remain the mathematical definition and Python's runtime.
