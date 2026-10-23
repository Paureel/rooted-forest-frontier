# Coupled continuation on the fifteen-leaf witness

The coupled continuation repairs the original fifteen-leaf witness at one of its two actual overlap-edge selectors. The other selector still has mass greater than one after its required further SPLIT. This finite result leaves a passing selector, so it does not refute every selector of the new continuation. Algorithm, Correctness, and Smaller base remain OPEN.

The compact executed record is `../../../results/algorithm-scaffold-adversary-coupled-summary-v1.json` (144,140 bytes). It retains original labels and graphs, source eligibility, every initial emission, actual further SPLIT cuts, overlap connected groups, Fitch source realizations, local zero/one-cut tests, typed budgets and recursive task multiplicities. The original pretest-only H2 witness and all its frozen records remain unchanged.

| Case and actual edge selector | Full recursive task charges | Exact task mass | Result |
|---|---|---|---|
| Original15, [5,7] | 1,1,4,4,3 | 2962867400/2947295521 | Fails |
| Original15, [7,9] | 1,1,4,5,6,3 | 158752208278600/160005726539569 | Passes |
| Parent19 contact, [3,4] | 1,1,4,6,6,3 | 157422208278600/160005726539569 | Passes |
| Parent19 contact, [3,29] | 1,1,4,6,6,3 | 157422208278600/160005726539569 | Passes |

The original two endpoint branches retain unit charge. Every other task pays all distinct actual source cuts, including the two pendant precuts and any solved-group cuts, plus the lower bounds required by other unresolved disjoint parents. No graph cut is credited twice, and identical pair signatures do not remove recursive tasks.

At original15 selector [7,9], an emission leaves the individually homeomorphic source components {1,4} and {5,6} overlapping. Their restrictions match, but their forest is not terminal. Polynomial minimum-change Fitch coloring gives three pieces on this group. Because it already has two source components, the exact additional source charge is one, realized by original source edge [26,28]. The induced six-leaf hard pair remains a separate unresolved query; its true full charge rises from five to six. That extra actual cut changes the pretest-only vector [1,1,4,5,5,3] to the passing vector in the table.

At selector [5,7], one initial emission leaves a non-homeomorphic parent overlapping another parent. The only remaining shared target edge is [7,9]. The instrument executes the actual two-sided normal colored-core SPLIT there, obtaining two one-cut emissions. Every resulting unresolved query is a sole bad parent, so its other-parent loss is exactly zero. The final vector [1,1,4,4,3] still fails: its integer numerator exceeds its denominator by 15,571,879. The passing selector [7,9] has numerator below denominator by 1,253,518,260,969.

The completed parent19 summary was a declared development data contact. The instrument reconstructed its original graphs and both actual shared-edge selectors before comparing the reported vector. Each produces the sorted vector [1,1,3,4,6,6] and the reported exact mass. In the relevant branch, two disjoint component pairs both refuse zero/one further cuts; each has lower bound two. With initial budget 12 and four actual source cuts, each recursive query therefore has budget 12−4−2=6. The instrument retains both queries. The contact lists three vertex-selector rows; this test reconstructs two shared-edge selectors and claims only the matching vector and mass, not a reconstruction of all three vertex selectors.

The new controls passed 27/27 checks before the pilot. They include an all-compatible overlapping quartet requiring one additional cut, a zero-cut twin, wrong Fitch/source charge rejection, typed-budget refusals, a sole unresolved parent with zero other loss, two unresolved parents with lower bounds two each, false extra-cut credit, and false multiplicity. Bounded exact cut enumeration is confined to the small control oracle. The tested continuation uses polynomial color assignment and original-source reconstruction for solved good groups, exact local zero/one-cut tests for isolated bad components, and actual colored-core SPLIT for bad overlapping groups.

The bounded pilot completed fourteen continuation states and fifteen recursive queries, with no unsupported consumer or state-cap refusal. Original15 took 0.0866 seconds and the parent19 contact took 0.1233 seconds on this machine. No extension, new graft census, extra independent replication, or broad toolkit-suite rerun was needed. The new source files passed their recorded hash checks, and the old delivery hashes still match.

The finite calculation tests this stated continuation and its actual source cuts. It establishes neither a complete faster algorithm nor a universal mass bound, and it supplies no algorithmic lower bound. The full safe integration and proof obligations remain open.
