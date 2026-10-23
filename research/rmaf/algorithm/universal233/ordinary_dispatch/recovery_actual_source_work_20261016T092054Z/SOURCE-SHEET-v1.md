# Source operation sheet

The source version is the pinned checker readonly pool. CoreProgram.lean and Work.lean have the same source bytes as the licensed functional package; their differing compiled files are recorded rather than interchanged. Every new meter's exact value theorem binds to the actual imported source constant. The source/olean identity records and the nine-producer body audit qualify these logical source results; they do not claim native IR correspondence.

| Source operation | Charged recurrence | Derived bound |
|---|---|---|
| CoreProgram.groups | leaf 4; node child work plus `4*(leftGroups.length+1)+4` | `16*(N+1)*footprint t` |
| CoreProgram.normalize | leaf 4; both children; same-color leaf case pays `4*(leftLabels.length+1)+12`, other match 8 | `32*(N+1)*footprint t` |
| CoreProgram.erase | actual address comparator; leaf adds8, node both children plus 12; early-stop suffixes may be overcharged | `32*(N+1)*footprint t` |
| CoreProgram.mixedCherry | leaf 2; both child meters plus 8, root pair value preserved | `8*footprint t` |
| unique-color filter predicate | meterFilter with Nat color comparison 4, then literal meterLength and comparison 4 | `16*(gs.length+1)` |
| CoreProgram.choose | actual groups, all predicates, ordered find with repeated filter/length, mixedCherry and 16 control slots | `128*(N+1)^3` |
| CoreProgram.attempt | address-list contains, erase,16 guard/record slots; successful continuation and 8 counter slots | explicit continuation bill plus `128*(N+1)^2` |
| finish output | detached map by reference, actual groups/flatMap label appends, outer detached-list append and 12 slots | `64*(N+1)^3` |
| CoreProgram.step/combine | normalize and choose, all actual branches,32 control/update slots; combine adds `4*(leftOutputs.length+leftRefusals.length+1)` | new `localCap N+2*B+4*(R+1)` |
| CoreProgram.run | q=0 still evaluates a step; each pruned continuation constructs its receipt and pays 4 slots | `16*envelope q (localCap N)` under Within |
| CoreProgram.fromTree | leaf color work plus 8; node both children, two address appends `8*(p.length+1)` and 8 slots | `32*(N+1)*treeNodes t+actualColorWork` when p.length+treeNodes t<=N |
| CoreProgram.generate preparation | literal first leaves/nodup; repeated leaves/count, source subtraction/min, fromTree and 16 slots; refusal 8 | frozen initialCharge plus exposed coloring |
| FinalCutRecovery.blockColor | exact contains/early stop/headD,8 slots per visited block, empty branch 2 | `32*(flattenCells+blocks+1)` |
| FinalCutRecovery.recover | prior derived raw input guard, literal P.length, new actual generator and 8 head/control slots; refusal 8 | finalSourcePolynomial times `2^(P.length-1)` on checked P |

Footprint bounds the current tree's label cells and original address cells, not merely its number of leaves. A selected group's origin length is proved from choose membership in the current tree before any attempt accepts. The duplicate-cut comparator traverses at most the selected origin length; arbitrary longer saved cut addresses require no accepted-payload premise. Erase compares each current address as its bounded first argument.

Within N q t d c is the frozen structural inequality `footprint t+d.length+c.length+2*q<=N`. Normalize and successful erase preserve the footprint bounds; the two new list heads are paid by the decrease in q. CoreWork.initial_within supplies this condition with N=inputResource of the original tree and the actual clipped budget. These are resource/value facts, not old cost assumptions.

Scalar slots charge fixed source operations. Contains uses the completed four-per-label comparison recurrence; address equality uses the completed four-per-Bool-cell recurrence. Leaves/nodup/all/filter/map/list-length/flatMap providers were read in their pinned source and reused without rebuilding them. All label/counter encoding and native execution interpretation remains external. String literals, nil/none constants and returned payloads are references; no byte serialization is hidden in these counts.

The original CoreWork.initialCharge is proved sufficient for non-color initialization. The new global localCap is four times CoreWork.cap at the same resource N; it is not presented as a proof that four times the state-dependent localCharge suffices. The full run pays actual receipt copies through an explicit recurrence, then uses the purely arithmetic envelope_closed theorem. The resulting coefficient comparison with the old polynomial occurs only after the new primitive source proof.
