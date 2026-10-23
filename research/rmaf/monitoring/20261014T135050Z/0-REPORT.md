# Fresh review of path, geometry, and assembly

The three reviewed modules pass their stated partial interfaces. I found no
semantic defect in PathStem, FamilyGeometry, or the three transition constructors
in FamilyAssembly. The composition theorem is a proof using the two existing
formulations, not an additional independent derivation. Full G2 remains OPEN.
The checkpoint prose needs the two scope corrections below before circulation.

This review preserves every author source. Exact source versions and commands
are in `source-manifest.json` and
`../../../results/triple-family-composition-review-replay.json`. All source
locators below refer to the retained copies under `snapshot/`, so later edits
cannot change the reviewed text. The reviewed parent report SHA-256 is
`40e2d564024ed2302aa374bdfaf967fa19ae170b5219e06e35520d5d6296a306`.

## Executed evidence

`exact_graph_check.py` was written and run after reading the target and frozen
control specifications, but before opening any of the three proof bodies.
It represents trees by explicit undirected adjacency and uses breadth-first
paths. It imports no author code and reads no author computed outputs. The
16 exact fixture comparisons passed; all 16 deliberately wrong results were
rejected. The receipt is `exact_graph_check.json`. These are independently
computed regressions of revealed fixtures, not unseen holdouts or a census.

The root-path cases include the incursion pair, an asymmetric tree with a real
opposite-child label, a singleton labelled root, a leafless root fragment, and
the gapped support. Assembly cases separately count the regions and root-absent
regions of the cherry close-both, extend-left, and extend-right constructions;
their tolls are 2, 1, and 1 when both children are open singletons. A manually
merged cherry checks only its stated finite fixture. A four-block graph fixture
keeps adjacent indices distinct and permits unused internal vertices; equal
color values themselves are checked in the Lean cost controls below.

Fresh compilation used only reviewer-owned `build-geometry/` and `build-cost/`,
with the workspace `bootloops-lean` wrapper and workspace `ELAN_HOME`. The old
TripleDP pilot took 1.014 seconds. The remaining individual compilations took
under one second each. All 17 declared stages passed their stated criterion:
14 accepted compilations and three rejected files containing four false
propositions. Source hashes were unchanged through the replay and matched the
retained geometry and cost receipts; the path work-file freeze also matched.

The main axiom inventories are separate: PathStem has 16 theorem audits,
FamilyGeometry has 8 theorem audits, and FamilyAssembly has 17 declaration
audits, comprising 13 theorems and four constructors (`closeBoth`, `adjoinRoot`,
`extendLeft`, `extendRight`). No audit depends on axioms outside `propext`,
`Classical.choice`, and `Quot.sound`. The exact forbidden-token scan found no
`sorry`, `admit`, custom `axiom` declaration, or `native_decide` in the accepted
sources or specified false-control files. Dependency inventories are retained
separately and do not increase the original author result counts.

The retained compiler failures name the false propositions, rather than an
import, parser, or unrelated elaboration failure:

- `logs/path-false.log`: the raw incursion implies a leaf in that child.
- `logs/FamilyNegative-dependency.log`: `0 = 1` for the open singleton's closed cost.
- `logs/cost-false.log`: `cherryClosed.blockCount = 1` and
  `adjacentSameColor.blockCount = 1`.

Their four matching true propositions compile. The path clean file uses exactly
the negation with the same Std import. The cost twins change only count 1 to
count 2, and compile against the freshly constructed family controls. The
FamilyControls singleton theorem provides the zero-cost twin for the inherited
family negative file. Path controls have seven audited groups; cost controls
have eleven audited declarations, including the manually constructed merge
fixture and the explicit distinct-label/same-color assertion.

## Semantic findings

| Object | Read statement and locator | Review |
|---|---|---|
| Root paths | PathStem:28–33 defines `RootHull` by a labelled descendant prefix and `openTrim` by `leaf a ∧ region a`; :35–46 relates this to `OnPath [] a v`. | The retained vertices are exactly on root-to-retained-label paths. The proof does not confuse LCA closure with path convexity. |
| Shrinking and labels | PathStem:78–89 assumes both `PathConvex region` and `region []` for subset and label equality. | Those hypotheses are necessary for general raw supports and are supplied explicitly. Labels cannot be introduced by an excursion through another leaf. |
| Leafless children | PathStem:106–124 states `(∃ v, openTrim leaf region (side :: v)) ↔ ∃ a, leaf (side :: a) ∧ region (side :: a)`. | This is exact child occupancy after trim. It does not assert that an arbitrary rooted convex raw region already satisfies the implication. The raw false twin demonstrates the distinction. |
| Restriction and discard | PathStem:128–149 proves pointwise trim/restriction equality and that the whole trim is empty when no selected label exists. | The first is a single-support identity. Neither theorem supplies a restricted family, reindexes blocks, assigns a DP state, or proves a family toll equation. |
| Finite specialization | PathStem:163–180 assumes boundedness, convexity, root membership, and a retained leaf. | The theorem keeps vertices in the actual finite tree and preserves its leaf-address membership. The wrapper records unique leaf values, although the geometric proof does not need uniqueness. |
| Hull composition | FamilyGeometry:9–21 states `OpenHull t R = PathRoute.openTrim (Leaf t) R` under `HasLeaf t R`. | Both inclusions follow from the respective least-convex/root-path properties. Nonemptiness supplies the root on the root-path side. Omitting it would equate the root-containing hull of an empty leaf set with an empty root hull. |
| Normalized openness | FamilyGeometry:23–43 composes `normalized_open_is_hull`, `normalize_retained`, and the preceding equality. | No extra family invariant is assumed. A retained normalized open region has no vertices in a child without one of its own leaves. This is geometry, not the still-missing charging/state correspondence. |
| Block identity | FamilyGeometry:45–56 uses a closed region's leaf witness and disjointness to distinguish its leaf-address set from other closed/open sets. | The nonempty witness prevents a vacuous empty-set equality. This is address-set distinctness; it does not establish disjoint value sets when labels repeat, or identify blocks by color. |
| Normalized count | FamilyGeometry:58–81 proves `labelledBlocks (normalize F) = closedCost (normalize F) + openCharge (normalize F).openRegion`, and empty-open pruning leaves `closedCost` unchanged. | This is bookkeeping in RawFamily, where closed cost is the parameter k. It is not an identification with the separately enumerated CostRoute family. |
| Actual finite index | FamilyAssembly:23–56 requires `elems.Nodup` and `∀ i, i ∈ elems`; `indexSum` concatenates separately tagged left/right enumerations. | Length counts all indices exactly once. Distinct tags cannot collapse even when labels or colors coincide. |
| Actual family invariant | FamilyAssembly:65–74 requires bounded, convex, leaf-bearing, disjoint supports covering every leaf, with `support i [] ↔ boundary = some i`. | Input families carry these explicit hypotheses. Each reviewed constructor proves every output field; none assumes that the assembled output is a valid family. All indexed regions must be live, including the optional root region. |
| Closed cost | FamilyAssembly:76–149 defines cost by length minus boundary charge, then proves `f.cost = f.closedIndices.length` and `i ∈ f.closedIndices ↔ ¬ f.support i []`. | The count interpretation is justified by the complete duplicate-free list and a proof that removing the distinguished index removes exactly one entry. Natural subtraction does not silently truncate: `boundaryCharge_le_count` proves the required bound. |
| Close both | FamilyAssembly:177–253 constructs the sum-index family, leaves the parent root unused, and proves exact count and cost. | Every child index survives, supports remain in separate children, labels persist, and the toll is precisely the sum of the two old boundary charges. The proof does not posit a block correspondence. |
| Add root | FamilyAssembly:274–323 defines support by `(i = o ∧ a = []) ∨ f.support i a`; it assumes old boundary `none` and convexity of the one enlarged region. | This adds only the parent root to one existing index. Old root absence gives disjointness. Restriction to a node tree makes the new root unlabelled. The geometric premise is transparent, not a hidden output-family premise. |
| Left/right extension | FamilyAssembly:325–367 supplies the preceding convexity premise using actual child-root membership, then proves counts and tolls. | These are actual constructors with full output proofs. Left extension charges only the right child's old open index; right extension charges only the left child's. Both preserve the sum of input block counts. |
| Label values | FamilyAssembly:369–408 proves per-index `hasLabel` preservation for close-both and root addition. | Together these establish the analogous statement for each extension by composition. The statements concern membership of label values; actual lifted support definitions also retain each leaf address. No color/mask admissibility theorem is supplied. |

FamilyModel and FamilyTrim were inspected only for the exact interfaces used
above and rebuilt as dependencies. This review does not replace their separate
fresh semantic review. In particular, RawFamily permits a leafless optional
open support and charges only its k closed supports; CostRoute.Family requires
every enumerated index to contain a leaf. A map between retained RawFamily and
CostRoute.Family, preserving labels, indices, root designation, and costs, is
still required. Both models cover all leaves of the supplied tree; adapting
them to an arbitrary strict relevant-leaf subset is not established here.

## Prose corrections

The reviewed checkpoint report is preserved under `snapshot/family/REPORT.md`.
Two sentences need correction; neither requires changing a theorem.

1. At parent REPORT:46–47, replace “the no-leafless-child corollary forbids
   assigning or charging such a fragment” with “The no-leafless-child corollary
   excludes all vertices of a child containing no leaf of the normalized open
   support. Connecting this exclusion to family restriction and DP charging
   remains open.” The theorem's conclusion is vertex absence; the source does
   not formalize an assignment or charging operation.
2. At parent REPORT:82–83, replace “The concrete singleton family has closing
   cost zero” with “The concrete singleton family has closed-region cost zero
   while open”. Closing a retained open singleton adds one in the cost model;
   the current phrase blurs two quantities.

The final paragraph's “accepted partial target” (REPORT:109) should also be
made consistent with the first paragraph's pending fresh acceptance status
when the parent integrates the completed reviews. The count and existing
scope statements are otherwise supported by the cited receipts. Detailed
referee and two-pass prose records are separate files in this directory.

## Remaining scope

Universal merge, the two directions of four-transition family correspondence,
restriction and live-index reindexing, the RawFamily/CostRoute representation
map, good-color/bad-mask legality, finite-address/graph hull equivalence, and
the Python table/backpointer connection remain OPEN. The manual merge fixture
and the pointwise child restriction lemma do not discharge those items. No
finite census was enlarged. The general BootLoops package suite, external
engines, and an extracted implementation were not tested by this Lean review.
