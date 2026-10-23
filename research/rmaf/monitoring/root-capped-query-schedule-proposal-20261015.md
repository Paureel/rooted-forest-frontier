# Unreviewed capped-query scheduling sketch

Root scratch, 2026-10-15. No new proof, test, acceptance or runtime claim.
Not sent to running authors. Potential consumer: the actual both-bad pair
continuation, once legal disjoint recursive tasks and budget identities exist.

For hidden local cut minima mu_i with certified lower bounds l_i, suppose an
actual recursive decision call at budget t has an inductively justified
cost C*c^t and succeeds iff mu_i<=t. The proposed procedure searches each
unknown minimum in increasing budgets from l_i to

    cap_i = b - sum(previously found minima) - sum(later lower bounds).

First reject if certified total lower bounds exceed b. Retain explicit signed
budget rejection; do not clip a negative budget to zero and query it. On first
success, its queried budget is the exact minimum. If all succeed, combine the
retained witnesses only through an actual reconstruction theorem.

Tentative cost argument: cap_i <= b - sum_{j != i} l_j. The increasing-budget
call cost is a geometric sum, with a constant depending on c>1. Two distinct
certified-positive tasks therefore reduce EVERY queried cap by at least one.
A sole unresolved positive task receives no such discount from its own
positive lower bound. A task with an explicitly constructible one-cut witness
and matching lower bound can instead be completed directly, charged its
polynomial construction cost, and removed while subtracting one from b.
This last route is different from asking an expensive query at budget b.

This would match the cheap/high pair possibilities: a cheap output with two
bad restricted pieces could use the two-task bound; if its cleared sectors
are both good, their known two-block local agreement might give a direct
one-cut completion for the whole bad parent retained by the opposite cover.
Prove all parent preservation, restriction agreement and paid-cut identities
before making that substitution. A positive optimum measured by an oracle
does not provide the witness or this procedure.

Pure setup/rejection costs must be charged separately, including zero-budget
and singleton-task cases. Do not state a c-to-negative-power cost bound for
an immediately rejected task. Charge all tests, failed calls, scans, repeated
raw outputs, local witness construction and reconstruction. Recursive call
budgets must strictly decrease from the actual solver's parent parameter.

The MAIN missing interface is legal independent task construction on a current
source forest Q whose target embeddings may overlap. Clearing selected target
vertices does not make all Q blocks target-disjoint. The existing two-tree
restriction/reconstruction theorem requires its explicit original embedding
premises; grouping an overlap graph may create source group hulls that overlap
even when the individual source components do not. A stronger forest-state
transport/reconstruction argument may be needed. This sketch supplies none
of those facts and must not be used as a full-algorithm runtime proof.
