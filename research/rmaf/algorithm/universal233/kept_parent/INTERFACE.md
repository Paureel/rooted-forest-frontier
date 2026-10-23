# Kept-parent interface

The author proof applies to every literal output of `CoreProgram.generate`. Its only original source hypotheses are the actual `partitionCheck (leaves S) [A,B,C] = true` and `pairwiseEmbeddings S [A,B,C] = true`. B's local coloring is arbitrary. Fresh nonauthor review remains required; all three main algorithm milestones remain OPEN.

Import `KeptConsumers` from an isolated build containing the pinned dependencies. `keepColor A B cb` is definitionally the frozen `Assembly.taggedColor A B (fun _ => 0) cb (fun _ => 0)`.

| Declaration | Inputs and conclusion | Source |
|---|---|---|
| `generated_keeps_A_C` | Actual original partition and embedding checks, arbitrary cb/q, membership of o in the literal output list. Returns one block with exactly A membership and one with exactly C membership. | `KeptParent.lean:90` |
| `generated_unique_kept` | Literal output membership, nonempty A, and `Keeps A o`. Returns a retained K, exactly one occurrence of K, and equality of every other list having A membership with K. Instantiate twice after `generated_keeps_A_C`. | `KeptConsumers.lean:39` |
| `restrict_same_members` | Equal original-label membership of K/A. Returns `restrict K T = restrict A T` for every original T. | `KeptConsumers.lean:55` |
| `restriction_agrees_same_members` | Returns equality of the original restriction agreement checks. An original non-homeomorphic A remains non-homeomorphic at K. | `KeptConsumers.lean:61` |
| `every_output_retains_paid_A` | The source checks, original A disagreement, and a supplied original local agreement with two pieces. Returns an unchanged local completion on the retained K and local charge `F.length - 1 = 1`. | `KeptConsumers.lean:80` |
| `every_output_retains_original_local_cut` | The source checks and a supplied actual one-cut original local certificate. Returns the same certificate on retained K, including the same original restricted source tree and its local address. | `KeptConsumers.lean:107` |

The paid consumers hold for every output, so a B-clear-output condition can be imposed by a later caller without changing their conclusions. The original target and source restrictions use the same labels throughout. `OriginalLocalOneCut` is a supplied completion certificate on `S|A`; it contains no assertion that the whole-source generator preserves A.

The source-cut lift in `FIRST-GAP.md` must precede a combined whole-source completion or an additional-cut recurrence. The local certificate preserves its address in the original restricted A tree; this package has not mapped that address into the whole original S tree.
