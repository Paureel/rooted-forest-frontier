# Source extraction record

Source: `research/rmaf/sources/baseline/split-or-decompose-v2.txt`, retained
v2 PDF-page markers. The following source bytes were opened during this run.

Core coverage definition, PDF p7, text lines371–372, verbatim:

> Say that a setC ={K1,...,Kn}of non-empty cuts is asplitting core
> for(Y,Z)if for every cutKthat splits(Y,Z)we have thatKrefinesK i for someKi∈C.

Read facts with their exact scope: Lemma1 (pp7–8, lines377–426) constructs
such a core on a binary phylogenetic tree, strengthening its induction to
maximum undirected degree3. Its printed sum is at base2. Branching rule1
and Lemma2 (p9, lines448–495) allocate one overlap edge between two source
components and split the other according to this definition.

Figure16 (p24, lines1318–1332) places rules6/7 after hard Whidden t2 and
before SPLIT. Lemma16 (pp25–26, lines1335–1409) treats triple common edge,
overlap chain, isolated third component, all-homeomorphic and remaining
single-overlap cases. Its residual bound is `(1,2,2)`. The ordinary convention
does not implicitly add rho (footnote2, p4, lines195–198).

The disjoint recursion rule and Lemma3 (pp9–10, lines501–553) use constant
depth prequeries and charge each unresolved local query with the lower
bounds of all other components. Source rule6 (p23, lines1256–1278) requires
an isolated homeomorphic third component; source rule7 (p24,
lines1279–1317) requires an isolated group of at least two homeomorphic
components. These are retrieved source imports. Their graph realization,
implementation and Lean consumer interfaces are open in this route.

Inference developed here: apply two independent source cores for each of
three common-edge survivor alternatives; apply all four combinations of
two overlap-edge ownership decisions in a chain. These constructions and
their finite receipts are the route's work, not attributed to the source.
