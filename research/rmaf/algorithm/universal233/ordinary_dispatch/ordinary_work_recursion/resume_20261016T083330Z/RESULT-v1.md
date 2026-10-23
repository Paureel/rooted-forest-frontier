# Ordinary callback recurrence

For every proper ordinary rooted binary tree pair, the literal ordinary callback tree has at most

\[
1024\,(n+1)\,(233/100)^q
\]

invocations, where `n` is the target leaf count and `q` is the residual cut budget. The counter includes the initial invocation and every ordered callback occurrence. A callback is counted even when it fails or repeats an earlier argument. The initial ordinary budget remains `q=k-1`; the external `k=0` guard and ordinary no-rho convention remain unchanged.

`ordinaryStepTrace_value` in `OrdinaryStepTrace.lean` identifies the companion value with the literal `FastOrdinary.solve` body. Its query list follows the actual proper/pretest/early order and uses the source cutoff callback. The one, high, Rule4 and complete hard2 paths consume completed trace packages. A common step contributes exactly one same-budget call and reduces the target leaf count by one. Every paid stage has the existing strict mass bound at `233/100`. `ordinaryCallNodes_bound` in `OrdinaryCallBound.lean` then uses outer budget induction and inner leaf-count induction; its statement contains no assumed callback mass or local-work bound.

The resumed `forestWork_cast` in `ForestNatWork.lean` and `forestWork_split` in `ForestNatSplit.lean` retain the exact Nat-to-Rat forest-sheet equality and separate local forest work from ordinary query charges. Their source and compiled checkpoint identities were preserved. This continuation supplies an ordered ordinary call recurrence alongside that separation.

The exact controls cover identical and malformed singleton inputs, a seven-leaf pair with a common contraction at zero budget, and the frozen repeated failed-callback fixture. The common example has one six-leaf query at unchanged budget and two total ordinary invocations. The repeated failed-callback example has two occurrences and charge two under constant-one charge. Both deliberately corrupted count-one claims were rejected by computation. The tests use the same Lean/source lineage as the proof and provide no independent acceptance.

## Remaining source costs

The invocation-count theorem leaves the full runtime claim open. The first missing source statement is a literal Nat nonrecursive bill for the beginning of `FastOrdinary.solve`: `DepthOne.proper`, `DepthOne.pretest01`, and the ordered `early` evaluation, including work performed when a guard refuses or a branch produces no answer. An accepted component must prove value equality to those source calls and a polynomial bound from structural and numeric input caps. A record assuming the desired whole-local cost bound would not supply that statement.

The complete ordinary source counter must also include common freshness/contraction/answer expansion, child materialization and answer checking/selection, Rule4 local work, the complete Rule5 local dispatcher, and forest overhead once per actual forest call. The completed non-Rule5 forest and allGood DP bounds remain available. The pinned Rule5 local-work packages explicitly stop before a complete local dispatcher bill. Numeric label growth, the bounded scalar/bit provider, and native or IR trace/cost correspondence remain separate missing premises. No new body for those components was owned here.

All main source/bit/payload/base and novelty milestones remain open. Independent reviewer acceptance remains open. Original frozen manifests, controls, failed attempts, alpha registrations, and source modes/inodes were preserved; the new directory contains the continuation and retained failures.

## Audit evidence

The completed author audit covers 497 imported problem modules and 12,619 stored declarations. Seven resumed or new producers retain full exact expression representations for theorem and nonproof bodies; four other fresh producers retain their source proofs and the existing qualified theorem-text omission, with actual references and axiom closure. The main counter, step binding and universal count proofs have full saved bodies. The axiom union is `Classical.choice`, `Quot.sound`, and `propext`.

The first four-module body extraction stopped at the required 3 GiB disk margin and remains failed. The second audit validated the two complete records already written, then extracted one remaining module per command. No limit was lowered. A versioned metadata amendment corrects the second audit's full-body module count from eleven fresh producers to seven full-body producers and four qualified producers; the original certificate is preserved. Independent reconstruction, local primitive/source completeness, bit/native checks and a blanket toolkit battery were not performed in this continuation.
