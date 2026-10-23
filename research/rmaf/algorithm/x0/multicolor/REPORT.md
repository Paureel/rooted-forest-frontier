# Multicolor X0 result

The falsifier found no counterexample through five source labels. It checked
5,703 tree/color inputs, including 2,718 three-color inputs, and covered all
31,540 source-valid monochromatic partitions. This finite result leaves the
universal core hypotheses and all three main algorithm milestones OPEN.

## Controls

All 19 frozen controls passed before the census. The seven literal plants
include the crossed quartet, homogeneous-cherry contraction with an original
singleton refinement, three distinct colors, three-color root/suppression
operations, an all-one-color root, a singleton, and the separate empty null.
Eleven deliberate corruptions were caught, and one insufficient-budget clean
twin returned no core and no feasible source partition.

On `T=((0,1),(2,3))` with colors `(A,B,A,B)`, omitting the first right mixed
branch returns the nonempty core `[[0],[1,3],[2]]`. The explicit source-valid
partition `[[0,2],[1],[3]]` does not refine that core. The clean prototype
returns both extremal cores, each realized by two original source cuts.
The corrupted core’s mass is `1/4`, below the desired `1/2`; coverage still
fails. A favorable mass alone therefore does not validate a core.

Wrong source charge, wrong rational mass, duplicate and zero cores, a cut at
the root with no source edge, duplicate and missing output labels, duplicate
source labels, missing color assignment, and a zero scored denominator all
triggered their named checks. The clean controls verify that these checks
can accept valid source data and actual group cuts.

## Census

The generator enumerated labelled nonplane rooted binary source trees on
`range(n)` and canonical color vectors under color renaming. The declared
tree and color-vector counts were checked before scoring. Every valid
monochromatic source partition was compared by refinement, including
24,337 partitions with more blocks than a smallest colored partition for
their input. The prototype never queried those minima.

| Labels | Source trees | Color vectors | Inputs | Three-color inputs | Valid colored partitions | Emitted cores | Budget queries |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 1 | 1 | 1 | 0 | 1 | 1 | 1 |
| 2 | 1 | 2 | 2 | 0 | 3 | 2 | 4 |
| 3 | 3 | 5 | 15 | 3 | 36 | 15 | 45 |
| 4 | 15 | 15 | 225 | 90 | 840 | 255 | 900 |
| 5 | 105 | 52 | 5,460 | 2,625 | 30,660 | 7,770 | 27,300 |
| Total | | | 5,703 | 2,718 | 31,540 | 8,043 | 28,250 |

Every one of the 8,043 unbounded emitted cores passed source-span and cut-graph
validation. Its lifted original blocks matched the connected labeled regions
obtained by deleting the reported original source edges, with no unlabeled
regions. Actual cut count equaled both the reported charge and `pieces - 1`.
The recorded executions include 2,594 detachments of groups containing several
original labels and 3,106 suppressions of the original root. These counts are
events across emitted-core traces; shared recursion prefixes can appear more
than once in those traces.

For every input and every integer budget from zero through n−1, the bounded
prototype returned exactly the unbounded cores whose actual costs fit the
budget. All 68,690 budget-feasible partition comparisons passed. The 12,661
budget queries with no feasible source partition were retained as refusals.
The instrument recorded 23,464 unbounded visited nodes, 83,208 budgeted visited
nodes, and 17,761 budget-pruned child attempts. No duplicate final partition,
empty unbounded core, or invalid source reconstruction occurred.

All nonempty unbounded inputs had exact raw mass `2^(1−r)` at base 2, and every
core had cost at least r−1. Raw and deduplicated masses also satisfied the
target bound at exact rational bases `233/100` and `3`. The empty null has zero
cut cost and is reported separately from the nonempty r≥1 hypothesis.

## Timing and retained data

The four-label pilot took 0.07955383299986352 compute seconds. Before n5,
the instrument recorded 5,460 planned inputs and 27,300 budget queries and
projected 30.888101559413677 seconds by multiplying the measured per-input
rate by an explicitly assumed sixteenfold slowdown. The extension took
3.712589583999943 compute seconds, including n1, n2, and n3. These timings
exclude JSON serialization and do not imply a parameterized complexity bound.

Original per-case data include source trees, colors, every valid partition
and its covering core indices, actual source cuts, group-expansion events,
source spans, rational masses, and every budget result. The original extension
JSON is 373,489,974 bytes; its losslessly checked gzip copy is 9,402,888 bytes.
Both remain local. A compact summary is
`results/algorithm-x0-core-summary-v1.json`; compressed controls, pilot, and
extension receipts use the same stems with `.json.gz`.

## Provenance and debts

`prototype.py` implements the pin directly and imports only standard-library
grouping and data-class support. It is an adversarial prototype and was not
read from a production generator or prover. `run_x0.py` compares its output
against the unchanged earlier X0 explicit source-span/partition/cut instrument.
The shared layers are the pinned operations, literal plants, and mathematical
source-partition definition. This test does not provide a nonauthor replay of
a future production implementation; future code selected against these data
needs a fresh independent verifier and controls.

The homogeneous-cherry refinement map, mixed-cherry coverage alternative,
unique-color detachment, original-edge realization under every suppression
case, universal mass/minimum-cost statements, and polynomial work per counted
node remain proof obligations. Finite visited-node and budget counts do not
discharge them. No Lean proof was constructed or audited in this task, and
the enumeration completeness argument has not been formalized.

The intended consuming call partitions one parent into three target-side
regions when clearing two edges in the overlap chain. The source tests do not
trace that graph-to-color interface, reconstruct the full rMAF algorithm, or
validate its complete paid recurrence. An emitted source core can coarsen a
target agreement partition while itself failing target agreement; the
comparator correctly tests source validity and refinement only. No improved
algorithm, exponent, or novelty claim follows from this finite no-fire result.
