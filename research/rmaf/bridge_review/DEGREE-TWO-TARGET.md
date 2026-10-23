# Actual degree-two refinement

Pinned by root on 2026-10-14 after the completed leastness checkpoint.
This is a new increment; preserve all completed sources and receipts.

## Consumer and target

Read this pin first and immediately write a workfile skeleton in `degree_two/`.
Then consult the toolkit and applicable proving/validation skills. Own only that
new directory and `progress/bridge-degree-two.json`, `results/bridge-degree-two-*`.
Do not import unfinished thesis or triple-transition work.

The consumer is G3/G4 in `pure_bridge/FORMAL.md` and the `clearRest` field in
`pure_bridge/lean/PureBridge.lean`. The full exchange still also requires G2,
G5–G7 and other interfaces; this task must not silently claim those.

Prove or refute the following ordinary, unaugmented, executable-model statement.
Let t and u be actual `RMAF.Tree` values with unique leaf labels. Let B be a
nonempty duplicate-free list of labels occurring in both trees, and require
`restrictionAgrees t u B = true`. Let v belong to `minimalVertices B t` and
have undirected degree exactly two in the graph induced by that exact support.
Degrees count actual parent/child edges, retaining unsuppressed vertices.

Construct two nonempty disjoint label blocks B0 and B1 partitioning B such that:

1. Each restricted block still agrees between t and u.
2. Their actual minimal embeddings are disjoint in each tree and are subsets of
   the corresponding original B embedding.
3. Both new embeddings in t avoid v.
4. Consequently every mark previously avoided by the B embedding stays avoided
   in its own tree, and every other disjoint piece stays disjoint.
5. Replacing B by B0,B1 in an actual agreement partition preserves the executable
   agreement predicate and adds exactly one component.

The first local statement should not require t and u to have identical full
label sets outside B. The whole-partition consumer does require the original
agreement/label conditions. Make each layer's hypotheses explicit.

To connect this to the component-level version of G3, separately derive the
needed fact for B contained in a component label set S: if the S embedding has
degree two at v, B's embedding uses v, and v is not a selected leaf occurrence,
then the B embedding has degree two there. Do not assume this silently.

## May assume

Use completed, hash-bound definitions and proven lemmas from RMAF, PureBridge,
GraphRegion, ExecutableConnectivity and the leastness checkpoint. In particular,
the actual extractor is connected, ambient-valid, terminal-preserving and least
among connected supports containing its selected occurrences. RootedIso and
sameShape_correct are available. Inspect actual statements before use.

The final leastness receipts are `results/bridge-leastness-summary.json` and
`bridge_review/leastness/acceptance.json`. Root owns aggregate theorem counts.

## Must not assume

Do not assume the two-piece refinement, cross-tree address identity, transport
through suppressed vertices, restriction associativity, preservation of AF by
arbitrary splitting, or correspondence between a target cut and a source cut.
Prove any such prerequisite actually used. An arbitrary split of labels in an
agreement piece need not be a two-piece agreement refinement.

Do not replace the original agreement predicate or MinimalEmbedding contract
with one that assumes the intended conclusion. No custom axioms, sorry, admit,
native_decide or failed elaboration may supply proof evidence. Conditional
statements must name every still-open graph/transport hypothesis.

## Frozen exact fixtures and failure conditions

Addresses below are Boolean lists, false=left and true=right.

- Root boundary: t=(0,1), u=(1,0), B={0,1}, v=[]. Degree is two. The two singleton
  blocks avoid v, agree, and cost one extra component. Address equality across
  the two trees is not the required transport.
- Suppressed path: t=((0,1),2), u=(2,(1,0)), B={0,2}, v=[false]. In t the exact
  B support is {[],[false],[false,false],[true]}; the degree at v is two. The
  split {0}|{2} has t supports {[false,false]} and {[true]}, while u has leaf
  addresses [true,true] and [false]. Omitting the unsuppressed v is a mutation.
- Global consumer: t=u=((0,1),(2,3)), blocks {0,2}|{1}|{3}, v=[]. The initial
  agreement has three components; splitting its first block gives four singleton
  components and preserves the other two pieces.
- Degree-three negative: t=u=((0,1),2), B={0,1,2}, v=[false]. Degree is three;
  avoiding v requires three singleton components. The proposed two-piece bound
  outside the degree-two regime must fail.
- Singleton and empty/absent selections must fail the degree-two/nonempty
  premises, not be assigned imaginary cuts. Repeated-label inputs must not be
  granted the unique-label hypothesis.
- Retain the prior joint-mark example in `pure_bridge/VERIFY_SPEC.json`:
  optima1,1,1,2 for no mark/each mark/both marks. The new result does not imply
  additive penalties or that all new marks can be cleared with one cut.

Freeze precise literals and the chosen checker interface before proof work.
Run the positive values and deliberate wrong-degree, missing-path, wrong-root,
cross-tree-address, overlapping-block and wrong-cost mutations first. A false
Lean proposition must fail for explicit falsity, with a positive twin; unrelated
syntax/type failures are diagnostic controls only.

## Independent routes and acceptance

Use the prove protocol: separate target pin and X0 adversary; no construction
before the exact in-regime hunt. Named distinct routes are (a) deletion of v in
the unsuppressed support graph and (b) rooted restriction/isomorphism transport
through the suppressed binary tree. Keep their fresh contexts separate until
their pinned outputs are complete. Use Astra xhigh for delegated work, at most
two active children, and wait for capacity rather than interrupting other work.
Pilot timings before expanding any census.

A nonauthor fresh reviewer must reconstruct the exact fixtures with its own
checker, rebuild final Lean sources, inspect every hypothesis at the actual
partition/clearRest use site, and check source/log bindings. Distinguish the
universal Lean result from bounded tests and ordinary mathematical arguments.

Licensed delivery forms: full local refinement plus actual agreement-partition
consumer; or a narrower formal intermediate with the exact missing transport
lemma pinned. The latter is partial and does not close G3/G4. If a frozen claim
fails in its stated regime, retain the exact witness and flag the pin erratum
before changing it; out-of-regime fires do not refute it.

No new larger search, full runtime claim or novelty claim is needed. Keep all
files and hosting local. Use a valid dashboard top status and string id/label
fields; precise qualifications belong in details. Register no aggregate counts.
