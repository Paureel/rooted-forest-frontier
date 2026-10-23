# Coupled finite continuation

This problem-specific continuation reuses the frozen independent graph/core lineage from its parent directory. It completes closed all-compatible overlap groups with polynomial minimum-change color assignment and original-source cut reconstruction, performs actual local zero/one tests on disjoint bad components, and executes an actual further SPLIT when a bad group still overlaps. It reports exact recursive-query charges and retains task multiplicity.

Use it to replay the two pinned finite cases, rather than to infer a universal algorithm. Read PIN.md and REPORT.md for the exact consumer and scope. The only bounded exact cut oracle is in controls.py, for tiny known-answer cases; the continuation contains no optimum oracle.

From the workspace root:

```
./bootloops-python research/rmaf/algorithm/scaffold_adversary/coupled/controls.py
./bootloops-python research/rmaf/algorithm/scaffold_adversary/coupled/pilot.py
./bootloops-python research/rmaf/algorithm/scaffold_adversary/coupled/package.py
```

Controls must pass before interpreting the pilot. The original fifteen-leaf records are preserved. PRE-RUN-FREEZE.sha256 records the exact algorithm and controls before this pilot; DELIVERY.sha256 records the completed local output. This instrument is deliberately local and problem-specific, and is not registered as a general toolkit package.
