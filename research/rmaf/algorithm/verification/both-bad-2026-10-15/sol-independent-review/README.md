# Independent both-bad verification preparation

This directory contains a fresh, one-shot prerelease graph/core instrument, exact literal controls, source-refiner bank, rational trace arithmetic, finite callback tables, and Lean provenance detector toys. It has no candidate imports and cannot certify the completed both-bad implementation before a separate root release.

Reach for instrument-v2.py to reproduce the25-case graph bank, supplemental-v2.py for literal addresses/guards/finite callback tables, toy_runner.py for resolved-name controls, and producer_runner.py plus AuditProducerFull.lean for stored-producer occurrence controls. The producer gate supersedes the stronger interpretation of the original merged-name inventory; v1 evidence remains preserved.

Outputs are exact integer/set/list/rational comparisons. Original cost is final block count minus1, source-core cost is original cut-address count, and ForestState local additional cost subtracts current source-list length. Failed theorem premises are reported separately from runtime refusal. PASS here means the named finite preregistered checks passed; it is not a universal theorem or candidate acceptance. Every output records denominators and scripts/source hashes; source/output failures are retained in PREPARATION and logs.

Trust gates: plants must pass and comparator mismatch must fail before controls; all25 fixed bank rows must complete with13650 source refiners; base exact output order must match hand frozen lists; Std false twin must fail; unused/private/coalesced stored custom axioms must be rejected; clean producer twins must pass; missing/duplicate/wrong source/import/type/body occurrences must fail. Mathematical/source correspondence is a separate post-release task.

Reproduction (from workspace root, use supplied wrappers):

```
./bootloops-python research/rmaf/algorithm/verification/both-bad-2026-10-15/sol-independent-review/instrument-v2.py plants --output /private/tmp/sol-both-bad-plants.json
./bootloops-python research/rmaf/algorithm/verification/both-bad-2026-10-15/sol-independent-review/instrument-v2.py bank --output /private/tmp/sol-both-bad-bank.json
```

The supplement and toy runners write their named evidence under this frozen directory; for replay after READY, copy this directory to a new separately named local replay directory and update absolute toy-adapter output paths there, recording adapter changes explicitly. Do not edit the READY evidence in place. No common toolkit code was changed; this instrument intentionally remains problem-local under TARGET ownership restrictions.

Candidate review remains sealed. Exact source560 release must be separately issued by root against READY and manifestSHA da001ef62039c916cf6db24f61c994094b5b1750f5be9130ddaf512ae5fbe20d. No self-release, no full algorithm/base/runtime/novelty closure.
