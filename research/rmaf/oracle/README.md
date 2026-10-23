# Rooted-MAF discovery oracle

This problem-specific Python instrument exhaustively enumerates leaf partitions
of two rooted binary trees. It records every minimum partition, checks rooted
restrictions and disjoint vertex embeddings, and constructs explicit `k-1` edge
cuts in each input for a valid forest. It is intended for small exact examples,
debugging candidate reductions, and finding counterexamples. It is not the
proposed faster parameterized algorithm.

The definition is pinned to Section 2, pages 3–4, of
[Mestel et al., arXiv v2](https://arxiv.org/pdf/2409.18634), dated 21 March 2026.
Trees are ordinary rooted binary, non-plane, with unique string leaf labels.
No extra root taxon is added. A forest partitions the shared labels, gives
equal rooted restrictions for each block, and has pairwise vertex-disjoint
minimal embeddings in both inputs. `k` is its component count; a cut witness
has `k-1` edges. Footnote 2 explicitly omits root augmentation in this paper.
There is no acyclicity condition. To test the rho variant, the caller would
explicitly add a common new root with a `rho` child to both raw trees and count
all resulting forest components; it is not silently interchangeable here.

Use this oracle when a proposed branching or reduction rule needs exact small
counterexamples. Existing BootLoops instruments were consulted first:
Annihilator concerns holonomic recurrences, the toolkit's enumerators concern
other mathematical objects, and JaCK & Jill computes Bayesian phylogenetic
evidence. None supplies rooted agreement-forest enumeration. Upstream tools,
verification scripts, and pins remain unchanged.

## Replay

From the workspace root:

```sh
./bootloops-python research/rmaf/oracle/oracle.py controls
./bootloops-python research/rmaf/oracle/mutation_check.py
./bootloops-python research/rmaf/oracle/oracle.py corpus --n 3 4 5
./bootloops-python research/rmaf/oracle/refine_cherry.py
./bootloops-python research/rmaf/oracle/sample_six.py
```

For an individual pair, save `{"a": nested_tree, "b": nested_tree}` and run
`oracle.py solve input.json`. A leaf is a string and an internal node is a
two-element array. Add `"forest": [[leaf,...],...]` to validate a proposed
forest instead. Invalid trees raise a named error; invalid forests return
`valid: false` with the violated condition and witness. A successful exit is
an executed computation, not mathematical acceptance.

The corpus CLI accepts leaf counts 1 through 6. Larger exhaustive searches are
outside this instrument's intended scope. The six-leaf experiment is a bounded
sample with a frozen seed and a 30-second compute cap. It does not enumerate
all six-leaf pairs. `oracle-v1.py` retains the exact source hash that generated
the initial corpus; the current oracle only adds a fixture option for the
deliberate comparator mutation and an input-size guard.

## Evidence and limits

The frozen `controls.json` was authored before the corpus was opened. Its five
hand optima, seven clean/corrupted forests, and three malformed input cases all
passed. The production comparator was also challenged with an intentionally
wrong expected optimum and exited unsuccessfully; its untouched clean twin
passed afterward. Receipts retain their denominators, hashes, rejection
reasons, and forest/cut witnesses.

The complete discovery corpus contains all 9, 225, and 11,025 ordered pairs on
3, 4, and 5 leaves respectively. It produced optimum histograms:

| Leaves | k=1 | k=2 | k=3 |
|---|---:|---:|---:|
| 3 | 3 | 6 | 0 |
| 4 | 15 | 180 | 30 |
| 5 | 105 | 3,150 | 7,770 |

All optimal leaf partitions are retained in `results/oracle-corpus.json`.
`results/oracle-corpus-n3-n4.json` preserves the first pilot receipt. The exact
generator uses canonical recursive leaf splits and restricted-growth leaf
partitions. It compares recursively pruned rooted shapes; minimal embeddings
are obtained by the union of paths from the block's lowest common ancestor to
its leaves. A valid partition's embeddings are extended to connected vertex
regions, giving a cut witness. The intended exhaustive argument is direct,
but no universal correctness theorem for this implementation is claimed:
independent implementation replay and Lean formalization remain required.

Two local ideas were refuted computationally:

1. Dropping the side-subtree branch and only cutting cherry endpoints fails.
   A six-leaf example with two off-path subtrees has unique optimum
   `{{a},{b},{c,d,e,f}}`, with cherry endpoints `d,f` together. See
   `results/oracle-counterexample-six.json` for raw trees and both cut sets.
2. Equality of restricted shapes alone is insufficient for common-subtree
   contraction. On conflicting triples, retaining one leaf of an equal
   two-leaf restriction changes the optimum from 2 to 1. Common pendancy is
   essential to the published reduction; the false rule omitted it.

The first endpoint-only rule died on four leaves at `t=1`. Its refined `t>=2`
version survived all eligible cherries on the complete small corpus, then
died on the fresh six-leaf sample. This is why the records say *open* for finite
survival and preserve the later counterexample. Neither finite survival nor
Python execution is Lean validation or a general proof.

`lineage.jsonl` records oracle birth and discovery contacts. These values may
not certify an algorithm selected or tuned against them. An independent
verifier must use a separate core (for example edge-cut enumeration and
rooted-triple signatures), and retain its own planted controls, comparator
failure, input convention, and untouched cases.

2026-10-14: created this problem-specific instrument after consulting the
BootLoops capability indexes; froze controls, executed bounded pilots, retained
counterexamples and receipts. No faster rMAF bound has been proved here.
