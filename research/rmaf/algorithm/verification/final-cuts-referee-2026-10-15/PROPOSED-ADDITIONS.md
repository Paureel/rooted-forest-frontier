# Proposed scope additions

Review-only excerpts from the proposed diff. Frozen reports remain unchanged.

## research/rmaf/algorithm/universal233/final_cut_recovery/RESULT.md

The executable `recover S P` checks the original ordinary source S and literal partition P, calls the actual completed generator at budget P.length-1 with one distinct color per P block, and returns the literal output's original cut certificate. Success checks only the source; original target agreement requires the actual premise `agreement T S P = true`, and minimum selection remains open. The author Lean proofs establish exact original realization, cost P.length-1, original agreement preservation, and the source-operation bound described below. Fresh nonauthor acceptance is pending. The complete solver, global faster-runtime proof and novelty milestones remain OPEN.

The future main caller must select its final minimum labelled agreement and invoke recovery once afterward; that caller remains open. `meterRecover_value` proves its exact value projection. `meterColor_value/work` and `total_color_work` pay the literal block scans at every original leaf. `final_work_bound` adds these to the completed full generator envelope, preserving all refused/pruned prefixes and actual receipt append work. The result is

    work <= F(S,P) * 2^(P.length-1),
    F=guardCharge+colorCharge+initialCharge+1+2*(cap(inputResource)+6)*P.length.

## research/rmaf/algorithm/universal233/final_cut_recovery/INTERFACE.md

`recover S P` checks distinct original source labels, the actual `partitionCheck (leaves S) P`, and actual `pairwiseEmbeddings S P`. It then calls the unchanged `CoreProgram.generate S (blockColor P) (P.length-1)` and returns its literal first output. The runtime record contains the partition and original cut addresses; the full component list is a proof witness. `recover` never enumerates set partitions or combines local cut sets. `blockColor` scans input blocks and returns the first label of the containing block.

The work theorem composes the completed all-prefix core envelope, not a minimum-output-only path. Its source-operation interpretation retains the helper-versus-fine-operation qualification in COST-MODEL.md. Ordinary scalar comparison is parameterized by original-label and counter bit lengths. The future main caller must invoke recovery once after selecting P; its actual call remains open. No theorem here pays for searching for P or selecting a minimum.

## research/rmaf/algorithm/verification/final-cuts-2026-10-15/RESULT.md

| Claim | Ruling | Source/evidence |
|---|---|---|
| Repeated per-branch recovery can omit the invocation factor from the summed exponential charge | REFUTED-AT-WITNESS | k=q3,c2,calls8:64>8; charge multiplicity only, with no tight runtime lower bound or tiny-fixture failure of generous F claimed |

