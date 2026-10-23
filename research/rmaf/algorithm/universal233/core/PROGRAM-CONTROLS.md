# Candidate program controls, frozen before program execution

Literal expected values come from the target pin, not this new program.

- Crossed quartet `((0,1),(2,3))`, colors A,B,A,B: exactly the two core partitions `{02|1|3, 0|13|2}`, each cost two; budget one returns none.
- Homogeneous cherry `((0,1),2)`, colors A,A,B: one core `01|2`, cost one.
- Same tree with three distinct colors: three singleton blocks, cost two.
- Three-color quartet, colors A,B,C,A: unique B and C detach, leaving the A pair; cost two.
- All one color: one unsplit block, cost zero, including original root.
- One original label: one block, cost zero.
- Duplicate original label: explicit input refusal.
- Lean negative controls: one-core crossed quartet equality and an original-root source edge claim must both fail compiler checking. A failure is expected and retained; success invalidates the harness.

These controls are DEVELOPMENT, authored by the program author from the pinned literal fixtures. They are not independent verification and do not replace the completed X0 census.
