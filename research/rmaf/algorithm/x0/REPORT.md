# X0 result

The fresh exact checks reproduced the retained forced-cherry and endpoint
rejections, caught a nonempty incomplete cover, and constructed eight actual
two-pendant-cut children from four retained input states. The checks establish
finite facts about these inputs. Complete algorithm, exactness, and exponent
milestones remain OPEN.

## Executed controls

The original battery passed 24 of 24 controls before any retained-input run.
Wrong rooted topology, intersecting vertex spans, duplicate labels, missing
labels, malformed duplicate tree labels, and unequal tree label sets were
rejected; their clean twins passed. Empty, singleton, identical, rooted-triple,
suppression, and component-versus-cut controls passed. The deliberately false
optimum comparator asserted 1 on a conflicting rooted triple whose measured
optimum was 2 and fired as required.

The exact rational comparison reproduced
`2896278200/2847396321 > 1` for `[1,1,3,4,4]` at `231/100`, and rejected its
deliberately false acceptance certificate. The clean twin `[1,1,4,4,4]` gave
`921759400/949132107 < 1`. These comparisons test arithmetic only.

Five supplementary source-predicate controls passed. They were registered
after the bounded run, before their own execution. They test the individual
Whidden t=1, Whidden t=3, rule4, and rule5 predicates, and an eligible hard
clean twin. A predicate can be true while an earlier global rule has priority;
actual hard-state admission checks all cherries in both orientations.

## Retained hard children

The one-state pilot took 0.006702792000055524 seconds and constructed two
children. The bounded four-state run took 0.0694664999999759 seconds and
constructed eight children. Each child records two actual pendant attachment
edges, three raw forest blocks, their restricted trees, the exact residual
optimum, every minimum partition and its spans, the tidying log, and expanded
minimum partitions checked against both original graphs.

| Retained state | Parent optimum components | Children | Residual cuts in each orientation |
|---|---:|---:|---:|
| n6 forced baseline | 3 | 2 | 1 |
| n7 forced baseline | 3 | 2 | 1 |
| n7 endpoint baseline | 4 | 2 | 2 |
| n7 endpoint after isolated endpoint | 3 | 2 | 1 |

The last state has one previously paid endpoint cut. Each listed child pays
two additional pendant cuts. All four states have no common cherries, and
every cherry in both orientations excludes Figure16 steps2a–d. Each selected
cherry has t=2. After singleton deletion and common-cherry contraction, every
child has TWO forest components. These inputs therefore do not test the
three-nonsingleton-component bottleneck.

The n6 and n7 forced-baseline controls both reproduce optimum components 3
versus 4 when the selected cherry must remain together. The n7 endpoint
parent and its isolated-endpoint child both retain only t=2 cherries and
exclude all earlier Figure16 steps in both orientations. One paid endpoint
cut does not force a cheap next Whidden case on this retained example.

## Missing cover

On the n6 baseline, the literal missed optimum is
`[[1],[0,2,3,4],[5]]`, with two initial cuts. The nonempty cover containing
only `isolate4` and `cut_all_two_pendants` has measured minimum three initial
cuts; neither child admits that optimum partition. Adding `isolate5` restores
the missed witness and the exact two-cut optimum. This catches a missing
branch using an explicit optimum, rather than merely detecting an empty list.

## Provenance and scope

`fresh_oracle.py` is new stdlib-only code. It imports no existing oracle
routines, and no existing oracle source was read. Partition enumeration uses
minimum-containing subsets, restrictions use induced hierarchical clusters,
and embeddings use explicit undirected vertex paths. The shared inputs are
the literal receipts and the mathematical definition. Receipt comparisons
are independent implementation replay, not untouched data for certifying
an algorithm later tuned against them.

The source definition and Figure16 priority were read in the retained v2
text, and the [arXiv identity](https://arxiv.org/abs/2409.18634) was checked.
`source-ledger-v1.json` retains exact page/line locators, copied source text,
and the source hash. The finite applicability conclusion depends on the
fresh checker’s interpretation of those source predicates.

No macro was constructed or universally refuted. No improved exponent or
novelty claim follows. No Lean theorem was authored or replayed in this X0
task, and the shared BootLoops validation suite was not rerun here; the toolkit
was unchanged. The parent task was asked to own any workspace-level suite run.
The next structural experiment needs actual hard children with three surviving
nonsingleton components, followed by fresh tests of a fully specified macro.
