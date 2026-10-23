# Controls pinned before universal state proof

All fixtures use the original RMAF Boolean partition/restriction/minimal-embedding checks through State.agrees. Kernel `decide`; no native_decide. Finite fixtures are controls, not universal proofs.

1. Differing target/source cherry addresses: T=((17,31),47), S=(47,(31,17)); F=[all]. True before/after contraction to fresh 89. Sibling swap accepted by RootedIso checker.
2. Final block contains extra label 47: the block [47,31,17] contracts to [89,47], expands to [17,31,47], and remains valid.
3. Endpoint reassignment: T=((17,31),47), S=(47,(17,31)), F=[[17],[31,47]] valid; replacement [[17,31,47]] is valid and no larger.
4. Singleton-source cleanup: T=((17,31),47), ss=[leaf17,node31 leaf47], F=[[17],[31,47]]. True. Remove17: target literally becomes (31,47), ss=[(31,47)], F=[[31,47]], cost remains zero. One-label cleanup yields none,[],[] and cost zero.
5. Refusals: absent endpoint 99, a=b, fresh collision z=47, repeated target17, and duplicate source label fail readiness/proper checks.
6. One-sided cherries: T=((17,31),47), S=((17,47),31) and its reverse. F=[[17],[31,47]] valid on the first state, but naive contraction produces an invalid state; synchronization is required.
7. Wrong cost: valid 4-label two-source state with F=[[17],[31],[47,59]] has cost 1, whereas |F|-1=2. Deliberately assert wrong equality and require failure.
8. Deliberately assert ready for a colliding fresh label, false one-sided transport, and a nonexistent singleton block; require kernel failure.

Production proof starts only after the true controls and false twins have executed and their logs have been retained. Fixture corrections are versioned and retained.
