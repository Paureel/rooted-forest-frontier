# Grouped full-current-state interface v1

Namespace Universal233.GroupedFullQuery. Import GroupInterface.

prepareOne reads a literal Problem (key, target, WHOLE source list), executes
ForestPretest01.pretest01, resolves original full-state cost0/1 globally minimal
answers, marks a proper rejection hard with universal cost>=2, and refuses
malformed input. prepare preserves order, duplicate occurrences and problem
payloads. prepare_malformed_refuses proves any malformed member refuses the
whole preparation; prepare_groups_exists and execute_nonrefusal discharge
refusal under actual grouped properness/partition/ownership.

callback actual p r invokes exactly GenericForest.solve actual p.target
p.sources r and annotates the returned original additionalCost. schedule is
the completed PaidQueries.schedule, unchanged. BelowIH parentq actual is only
forall r<parentq, LocalOrdinaryIH r actual. FullStateSchedule proves soundness,
minimum and witness-relative completeness at the actual allocated r without
assuming correctness at larger ordinary budgets or supplying a minimum oracle.

Under original full-state properness, a checked label-group partition, literal
current-source ownership and CrossClear between groups, grouped_sound proves
original full-state validity, exact concatenated cost, paid budget and global
minimum length. grouped_complete and grouped_feasible_iff prove exact bounded
feasibility. No target clearance is required inside a group.

abc_geometry constructs [A++B,C] from an original [A,B,C] source partition,
an actual original source partition P refining it, and only original A-C/B-C
target-clear guards. It permits arbitrary target overlap inside AB and arbitrary
C topology. original_grouped_complete lifts the actual grouped result back to
an original agreement refining P, no larger than any original feasible witness
refining P. original_grouped_paid_budget converts the full paid identity
paid=P.length-1, paid+residual=parentq into the original q=k-1 budget.

bad_source_positive derives positive group cost from a bad actual current
source tree. kept_bad_group_positive derives this from an actual kept original
source block K in P whose original target/source restrictions disagree.
kept_AB_C_badSlots derives two nonzero scheduler slots from kept A and C and
their original bad guards. No Cgood premise occurs. The more general grouped
consumer accepts any proved two-nonzero-group condition; it does not infer that
condition from overlap alone.

fullTrace is the existing meterSchedule's actual (problem,residual) trace.
fullTrace_actual_group proves every query retains its actual local target,
WHOLE owned source list, original group key and strictly smaller residual.
fullTrace_mass applies the generic badSlots theorem to this actual trace;
actual_outer_mass gives mass<=c^-1 at any enclosing parent budget, for c>=2,
even with early failure. original_kept_bad_mass discharges the mass guard
from the actual kept A and C badness.

Remaining integration: establish these source partition/refinement, retained
bad-block and original cross-clear guards for each desired fast-hard2 output,
and dispatch this consumer with the parent's actual total ordinary callback
and its strict-budget IH. These guards are explicit, not assumed automatic.
No complete fast solver, improved base or independent acceptance is claimed.
