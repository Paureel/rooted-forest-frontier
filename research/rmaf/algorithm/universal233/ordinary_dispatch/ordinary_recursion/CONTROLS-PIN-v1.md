# Actual recursion controls pinned before execution

For the rooted crossed quartet T=((0,1),(2,3)), S=((0,2),(1,3)), the actual scaffold at cut budget 1 must return none, and at budget 2 must return an original valid three-block forest. Identical quartet inputs at budget 0 must return one block. Mismatched single-leaf label inputs must return none.

Graft the shared cherry (4,5) onto the crossed quartet in both trees. The depth-zero/one pretest must reject this six-label pair; the actual first cherry selector must return the common (4,5) cherry. At budget 2 the recursive contraction/expansion path must return an original valid three-block forest. Its unchanged-budget contraction must reduce target labels from six to five.

The kernel must reject a claimed quartet forest at budget 1, reject a claimed two-block quartet answer at budget 2, and reject a claimed refund that leaves the contracted target label count unchanged. These controls test the actual program and measure, not a runtime recurrence or improved base. Retain an exact timeout or disk-floor stop without mathematical refutation credit.
