# Independent scaffold adversary

This one-shot problem-specific instrument reconstructs explicit rooted source cuts, restrictions, minimal vertex spans, source-rule eligibility, normal colored-core emissions, and exact whole-forest zero/one-additional-cut tests. It imports no existing rMAF evaluator. It remains local and deliberately outside the general BootLoops toolkit, whose scope excludes problem-specific evaluators.

Use it to replay the pinned scaffold falsification at c=233/100. The program reports exact cut charges, rational masses, complete pretest refusals, and separately scoped H1/H2 results. A failed source guard excludes a candidate from the counterexample denominator; matching component topology alone never proves a terminal forest.

Run from the workspace root:

```
./bootloops-python research/rmaf/algorithm/scaffold_adversary/controls.py
./bootloops-python research/rmaf/algorithm/scaffold_adversary/source_controls.py
./bootloops-python research/rmaf/algorithm/scaffold_adversary/group_mutations.py
./bootloops-python research/rmaf/algorithm/scaffold_adversary/pilot.py
./bootloops-python research/rmaf/algorithm/scaffold_adversary/package_witness.py
```

The literal controls must pass before interpreting output. `PRECONTACT-FREEZE.sha256` records what was frozen before candidate-source contact; the workfile records later adapter construction and declared input contacts. No proof of a universal core theorem, completeness of an alternative algorithm, or lower bound follows from this finite falsification.
