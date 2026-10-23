# Frozen wrapper controls v1

Frozen before executable wrapper or proof runs. Same-lineage development checks; independent root acceptance remains pending.

1. Singleton original inputs T=S=leaf 7: selected q=0, one query trial, one final recovery, zero cuts, one component.
2. Identical original fork T=S=node(leaf 0,leaf 1): q=0, one trial and one recovery.
3. Three-label disagreement T=((0,1),2), S=(0,(1,2)): selected q=1, retain trials q=0 failed and q=1 successful, two components and one original cut, exactly one final recovery.
4. Four-label published-in-package leftTree/rightTree: selected q=1, failed q=0 retained; one final recovery and exact cut/component conversion.
5. Malformed repeated labels T=node(leaf 0,leaf 0), S=same: no queries, no recovery, no output.
6. Unequal labels T=leaf 0, S=leaf 1: malformed refusal as above.
7. External component convention k=0 refuses before any query; q=0 is valid for singleton k=1.
8. A synthetic decision stream failing at q=0 and succeeding at q=1 has exact sum-of-query charges 1+2=3 for c=2 and coefficient 1. The false bound dropping failed trials (3<=2) must be rejected by Lean; the true full bound must pass.
9. Corruption control: claiming cuts=components on the singleton output (0=1) must be rejected by Lean; the clean cuts+1=components statement must pass.
10. Corruption controls for source hash and axiom audit: wrong SHA256, missing/duplicate producer row, and a fresh direct custom axiom must be caught. True 2+3=5 compiles; false 2+3=6 rejects.

Pass criteria are exact equalities and explicit expected compiler rejections. Any control miss is FAIL_RETAINED. No measured timings imply scientific closure.
