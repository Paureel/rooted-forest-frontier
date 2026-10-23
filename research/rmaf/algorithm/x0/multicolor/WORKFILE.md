# Multicolor core X0 continuation

Status: OPEN. Theory-finding adversarial tests only. All three main algorithm
milestones remain OPEN. No Lean proof construction.

## Scope

Read NEXT-MULTICOLOR-CORE-PIN.md first on 2026-10-15; then wrote this skeleton.
Own this directory and results/algorithm-x0-core-* only. Preserve earlier X0
receipts and manifest. Do not read unfinished prover work.

## Execution sequence

1. Freeze pin plants, exact rejection criteria, and census scope.
2. Write a falsifier prototype separate from the existing fresh reference.
3. Execute plants, missing-branch corruption/clean twin, wrong-cost/mass,
   source-span validity, reconstruction, and boundary controls.
4. Pilot four-label colored cases; record denominator and timing before n5.
5. Exhaust canonical colorings and all source-valid monochromatic partitions.
6. Retain exact fire witness or finite no-fire and universal/Lean debts.

## Evidence

Frozen seven literal pin plants, eleven named mutations, and the full census
scope before prototype execution. Prior X0 reference and manifest hashes are
recorded in provenance-v1.json. No production generator or unfinished prover
work was read. The toolkit has no multicolor source-cut generator; the new
one-shot prototype is required to test the pinned operations directly.

Known-answer battery executed first:

```
PASS controls: 19 / 19; 0.003915708000022278 seconds
```

The deliberately omitted mixed branch misses the explicit source-valid
partition [[0,2],[1],[3]], and the clean twin covers both extremal partitions.
False cut charge, false rational mass, duplicate/zero cores, invalid root cut,
duplicate/missing output labels, duplicate source labels, missing color label,
and zero scored denominator were caught. Budget zero on the crossed quartet
correctly returns no cores and no feasible source partitions; it is a clean
refusal control, not a vacuous unbounded pass.

Four-label pilot executed before any n5 case:

```
FINITE-NO-FIRE: 225 cases; 90 three-color cases; 840 / 840 original partitions covered
255 cut-realized cores; 900 budget queries; 0 duplicates, 0 zero unbounded cores
0.07955383299986352 compute seconds
```

timing-extension-decision-v1.json records the pilot measurement, frozen n5
denominator 5460 and 27300 budget queries, an explicit assumed 16-fold
per-case slowdown, and the resulting projection before n5 execution. The
projection is far below two hours; only n1,2,3,5 extension is launched.

## Limitations

Finite partition coverage does not prove universal graph, refinement,
generation complexity, or consuming algorithm correctness.

## Executed extension

```
FINITE-NO-FIRE: 5,703 total n1–5 inputs, including 2,718 three-color inputs
31,540 / 31,540 original valid monochromatic partitions covered
8,043 actual-cut cores, 28,250 budget queries, 0 failures
```

The n5 census alone has 5,460 inputs, 30,660 partitions, 7,770 cores and
27,300 budget queries. Exact costs, source cut graphs, original-label lifts,
spans and all finite refinement comparisons passed. All raw base-2 masses
equal the desired bound; bases233/100 and3 also pass. Min cost≥r−1 holds
on every emitted core. The separate empty null is not scored under r≥1.

The extension took 3.712589583999943 compute seconds after the recorded
30.888101559413677-second projection. Prior X0 files and manifest remain
unchanged. The large detailed JSON receipts were losslessly gzip-packed,
restored hashes checked, and originals retained. Summary and packing receipts
are results/algorithm-x0-core-summary-v1.json and packed-v1.json.

README.md documents a fresh-output replay adapter; its 19-control replay
executed successfully without altering the frozen core or comparator code.
REPORT.md records every scored denominator and all universal/Lean/interface
debts. No new proof or production algorithm was constructed.
