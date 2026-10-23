# State reduction interfaces

| Consumer | Exact proved input | Delivered assertion |
|---|---|---|
| Initial state | proper (some T) [S] | new agrees equals original RMAF.agreement for every F |
| Singleton detection | actual agrees T ss F and leaf a in ss | [a] occurs once; every a-block equals [a] |
| Reduced singleton state | same actual inputs | literal restrict/erase transforms satisfy actual agrees |
| Singleton reconstruction | proper original T ss, leaf a in ss, actual reduced G agreement | [a]::G satisfies original actual agrees |
| Budget | arbitrary original/reduced agreement and leaf membership | exact additional cost equality; same budget q |
| Progress | original actual singleton-source agreement | labels cleanup length +1 = original labels length |
| Cherry separation | actual original state agreement and actual target cherry | separated endpoint blocks force an endpoint singleton |
| Cherry restriction topology | proper labels, actual cherries independently in T and S, restrictionAgrees on B containing a and omitting b | original restrictionAgrees on b::B |
| Cherry replacement embeddings | statement in OPEN-CONSUMER-v1.md | OPEN |
| Full common-cherry transition | replacement, literal contraction and expansion required | OPEN |

Consumers.lean applies the completed interfaces to the pre-registered arbitrary-label fixtures, including final singleton cleanup and differing cherry addresses. It also checks an actual valid two-source state whose additional cost differs from |F|-1. All displayed equations are Lean propositions compiled by the replay. No desired reduction, safety, source-history, or reconstruction assertion is supplied as a State premise.

Dependency scope: original research/rmaf/lean/RMAF.lean and the completed restriction_bridge/Restriction.lean, Embedding.lean, Partition.lean. The source hashes are checked against restriction_bridge/replay/20261015T090816Z/certificate.json. Import-name changes are recorded explicitly. No unfinished pair_assembly, kept_parent, review, or active candidate is imported.
