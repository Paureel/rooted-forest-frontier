# Actual original-source constructor and nonrefusal interface

This package consumes original trees and literal original addresses/lists.
It constructs the frozen guarded caller's Setup, rather than asking a caller
to supply an abstract common-cut or marked-solver certificate.

`buildSetup T S X Y p` executes the original proper-label checks, both checked
X|Y partitions, nonroot p, the original source subtree lookup and its actual
descendant-label permutation with X, and the actual target incident-arc list.
Only a singleton incident list is accepted. It computes actual representatives
as list heads, fresh labels max(original labels)+1 and +2, all four unmarked
restrictions and all four explicit marked restrictions. Its proof fields are
only actual input guards/lookups. It stores no minimum, cover, projection,
gluing, saving or runtime conclusion. No noncomputable witness is used in the
runtime constructor.

`original_split_from_incident` derives the actual target nonroot original cut
with descendant labels X OR Y, from the singleton incident list, proper
original labels and checked X|Y. The other original cut is the actual source
lookup p. `buildSetup_complete` proves success for those original guards;
`buildSetup_identity` proves the resulting T,S,X,Y are the actual input values.

`actual_outside_one_from_three` starts from actual checked [X,C,[c]], both
original embedding checks, good C, an actual original target cherry a,b and
actual original source path predicates for a nonroot pendant containing c.
It derives the outside [C,[c]] AF by literal clipping. Its topology cannot
agree as one block: a target cherry would prune to a source cherry, whose
original pendant exclusion contradicts c's presence. An actual ordinary
depth01 test therefore finds a one-cut globally minimum answer. Outside
minimum one is a theorem result, never a field or antecedent.

`actual_source_nonrefusal` joins those results with the concrete `runSource`.
`actual_source_bounded_solver` derives an actual bounded exact inner answer
under SourceIH only at the actual sourceJobs list. The frozen caller supplies
the marked outside depth01/cost-two witness and SAME-list reconstruction.
`source_job_progress` proves every actual child pair is proper and its budget
strictly drops by one. No recursive solver is supplied by the IH interface.

The global source dispatcher must still instantiate every printed primitive
guard and parameter from its actual admitted/common-split selector. This
release does not assert that all remaining source states reach this case.
The fine source-operation bridge, complete mutual solver/runtime and once-only
final cut recovery remain outside this scope. FIRST-GAP-v1.md prints the call.
