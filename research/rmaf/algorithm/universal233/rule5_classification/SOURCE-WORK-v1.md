# Local source work

`SourceWork.lean` bounds the full four-way comparison-call trace of `sameShape`
by the product of the two original tree sizes. Short-circuit evaluation can
skip comparisons charged by that trace. The worst membership-scan trace of
`restrict X T` is at most `treeSize T * (X.length + 1)`.

The large and size-two selectors inspect at most the two actual source
pendant arcs under `admitted`. The outside selector scans at most the actual
source cherry count. It repeats the good-core restriction test for each
candidate; that repetition is included when estimating its work. Each shape
and restriction test uses original labels. The five-child cases materialize
five source forests, each with three permanent parts. Case1 materializes the
one hard-two source forest. Pair cuts come from the original finite terminal
arc finder.

These local scans and constant-size child lists add polynomial local work to
the completed cherry-branching interfaces. The trace bounds and candidate-list
bounds compile in Lean. This release does not prove a source-work recurrence
for a complete recursive Rule5 selector, because its remaining Figure15
classification is open. The parent must include guard computation, state
normalization and actual recursive calls when proving the whole algorithm's
work bound. No global branching base follows from these local counts.
