# Additional selected-edge literal controls v1 — preregistered before execution

Constructed by hand from public edgeOK, independent of candidate. Original source S=(A,(B,C)) with source-disjoint parent subtrees.

## S8 good sectors

A=((0,2),1), B=((3,5),4), C=(6,7).
T=(((2,((0,1),3)),(4,5)),(6,7)).
P=012|345|67.
Expected selector is edge(00,001), with Ainside={0,1}, Aoutside={2}, Binside={3}, Boutside={4,5}. Each parent has 2 occupied regions at each intersection vertex00,001, so no vertex choice. All four sector hulls clear the opposite whole-parent hull. All sectors are rooted-good (sizes1 or2). Both A/B rooted-bad, C good/clear.
Expected original AF F=01|2|3|45|67, globalcost4, no q3 AF. Expected both literal source-core q3 probes succeed with one output each. Source-generation fixed parent tags cost2, one sector split costs1. Exact output order/cut addresses will be frozen from hand simulation in a separate table before first core run.

A-only crossing original AF at edge001: F_A=02|1|3|45|67 is source-valid and target-valid: pair02 uses edge001, all B pieces are sector-contained. It must be covered by splitB core, not assumed covered by splitA. B-only crossing: F_B=01|2|35|4|67 (pair35 crosses edge001) covered by splitA. Both-crossing partition F_AB=02|1|35|4|67 has disjoint source hulls but overlapping target hulls at00,001, and fails original AF. Whole P fails rooted agreement.

## S9 bad cheap sector

A=(((0,2),1),3), B=((4,6),5), C=(7,8).
T=(((3,(((0,1),2),4)),(5,6)),(7,8)).
P=0123|456|78.
Expected selected edge(00,001), Ainside={0,1,2} rooted-bad, Aoutside={3} good; Binside={4}, Boutside={5,6} both good. A and B bad, C good/clear. Both literal source-core q3 probes succeed because each partition into sectors can be obtained by one local source cut. Minimum original AF needs at least A2+B2+C1=5 blocks, possibly more due bad Ainside; exhaustive 15*5*2=150 source refiners determines exact minimum. This initial control preregisters sector topology, not an unsupported minimum or planner trace.

## S10 both probes fail

A=((0,2),(1,3)), B=((4,6),(5,7)), C=(8,9).
T=((((2,3),((0,1),(4,5))),(6,7)),(8,9)).
P=0123|4567|89.
Expected selected edge(00,001); Ainside={0,1}, Aoutside={2,3}, Binside={4,5}, Boutside={6,7}; both parents bad, all sectors good, C good/clear. Each sector split of an alternating source quartet needs at least2 source cuts, so with fixed-parent2 both q3 probes fail. Source refiner denominator15*15*2=450 exceeds v1 per-pair400 cap: amend cap for this one exact fixed case to450 (no broad search). Outputs at q4 expected raw costs4; source generation may retain duplicates, all occurrences count.

## Domain guards

S8 with C=[]: nonempty-P premise fails; absent label C={99}: partition fails; C={1,6,7}: source partition fails by overlap. These failures are theorem-domain classifications unless actual runtime source later supplies a guard. S8 swap A/B list order retains same selected edge and semantic ownership; source-core tags/order change and need separate exact occurrence expectations.

Scope: these are independently constructed predictions to be checked, not candidate behavioral facts. Any mismatch stops the affected control and receives a preserved correction amendment before rerun.
