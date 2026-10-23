# Producer-control expectations, PRE-CANDIDATE

Frozen before any Lean control execution. Inputs in producer-controls/ are new original fixtures.

- SolCleanA and SolCleanB individually compile from Std, each stores exactly one same-name/same-type True theorem SolSame.token; either import order audits both occurrences and passes.
- SolFalse does not compile; Nat1=2 is false.
- SolHostile compiles, stores SolSame.token as an actual direct axiom, plus hostileOwnClean theorem. Audit rejects it alone and with SolCleanA in each import order, regardless of the merged resolved origin.
- SolUnused compiles; its unused direct custom axiom is rejected while own clean theorem also exists.
- SolPrivate compiles; private hidden axiom is rejected, and generated recursive/equation declarations using hidden are all retained in stored-array inspection. Direct axiom and generated dependent occurrences must both be visible.
- Audit row index/name inventory must cover each stored producer array exactly once. Deleting/duplicating a row, deleting/duplicating an inventory name, changing type/body/import bytes, or changing pinned source bytes must be rejected. Clean twin passes beside each mutation class.
- Installed Std/library source/olean hashes may be pinned rather than rebuilt. Scientific source claims require independent exact-source rebuild after RELEASE and all stored producers audited; these controls alone make no scientific assertion.
- First pilot only: compile CleanA then run ProducerAudit on CleanA, each process<=30s. Subsequent fixed battery uses the measured30s cap for each subprocess; no unbounded loops/census.
