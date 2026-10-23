# Consumer and certificate audit contract

This file records required interfaces, not a proof construction. It was written while the separate X0 run was active, before either construction route starts.

## Call-tree object

A certificate names the actual F1/F2 state, current cut budget, ordered selected pair, first applicable source rule, batch cut legality, inherited and newly created physical protections, and every resulting normalization. It counts an invocation once even if normalization loops several times. Failure at negative budget precedes success. All permitted legal children must be present; a deterministic allowed tie choice certifies only that tie policy unless the proof covers every permitted choice.

Analysis annotations P,Q are separate fields with a source phase/frame and a specified assignment rule. Any proposed change to these annotations is an analysis amendment requiring closure, not a physical algorithm mutation. A raw physical state without a source-history or validity proof is labelled local, not reached.

## Frontier imports

For each frontier exit, report its budget decrease, actual remaining budget, physical state validity, proposed P,Q, and the precise induction statement invoked. An empty-credit flag alone does not authorize an exit: the induction domain and history/annotation interpretation must admit that state. For credited exits, state and prove the stronger allowance rather than silently substituting the outer empty-credit hypothesis. Actual negative-budget invocations are terminal and counted directly.

The reviewed empty-credit majorant is applicable only after those per-exit imports are admitted. If the C prefix has expanded-call count V and L empty-credit exits at budget decreases d from C, its majorant is `alpha*2^(K-1)*sum(2^-d)+V-3L`. The mass and intercept conditions in TARGET.md are sufficient; exact coefficient/intercept tradeoffs are also licensed if checked on the declared alpha/budget domain. These formulas do not establish a source-valid prefix.

## Final use sites

1. A starts with budget K-1 and inherited nonempty credits. The desired allowance is `alpha*2^(K-2)-2`. Justify it independently or deliver a compatible substitute.
2. B cuts the actual three pendant edges and resets credits, so its nonterminal allowance is `alpha*2^(K-3)-3` when the explicit empty-credit hypothesis applies. Handle terminal budgets directly.
3. C starts with budget K-1, retains inherited protection and protects the retained endpoint. Its allowance is at most `alpha*2^(K-3)+2` in the sufficient interface. Include inside-b and outside-b source histories and all normalization paths.
4. Compose exact counts with the parent invocation. The target remains `alpha*2^(K-1)-2`; changes of constants or exponent must be declared and cannot silently satisfy this consumer.

No acceptance at these sites supplies the entire global induction, O(n) per-invocation implementation, or conversion to the campaign's unaugmented component parameter.

## Independent route commitments

The protection-ancestry route must organize by creation and transport of physical protection, including ancestry through credit resets, suppression, common-subtree merges and component-root removal. It must give falsifiable candidate invariants, a corpus consistency table, three sharp attacks and explicit exceptions.

The affine/potential route must organize by exact local obligations and sound certificates, with no assumption that an unrestricted abstract transition table is source reachable. It must separate algebraic feasibility, source extraction, and induction-domain closure; give its own candidate statements, corpus consistency table and three sharp attacks.

Neither route reads the other's unfinished artifacts. A new verifier reads the pin before writing its own skeleton and evaluator, then rules on every item above. A finite NO-FIRE, a source-model interpretation and a formal theorem with hypotheses are separately labelled.
