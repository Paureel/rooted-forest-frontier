# Specific second-exchange transport v2

Status: target read; adversary before proof. Earlier edge-route sources and receipts remain frozen.

1. Freeze original-spec input and controls; reuse the v1 independent graph oracle only after its fixed controls, with outputs redirected inside this new scope.
2. Reproduce concrete optimum and both cutsets; build actual yielded G and validate original edge IDs and endpoints.
3. Catch the planted map error; test the detached-rho component-root variant.
4. Hunt geometry-specific transport failures in a bounded measured sample, counting valid geometries and residual-cut premises separately.
5. Prove the specific structural/yield transport statement if possible, or isolate its smallest open lemma. No AF normalization or general suppression transport assumed.
6. Verify new formal statements and retain complete controls, hashes, and receipts for a later fresh review.

Adversary controls executed before proof: inherited fixed controls passed with outputs redirected to this v2 directory; concrete optimum 2 and both 2→3→2 sequences passed; exact endpoint-map corruption rejected; four detached-rho residual-cut cases passed. Transport comparison checks final yielded node IDs, labels, and parent endpoints exactly, in addition to shapes and both whole-component and descendant-root label fragments.

Pilot n=5, seed 622, 20 shuffled pairs: 0.02514 s and zero reached 2B states. This is zero transport evidence. Under stationary input cost, 3,000 pairs project 3.77 s; the actual transport cases can add overhead, so the bounded run will retain its measured time. Before extending n=6, run its separate pilot. No large enumeration is planned.

N=6 pilot: 20 pairs, 0.03630 s, zero 2B premises. A bounded 2,000-pair run projects 3.63 s from that measured input rate, with transport overhead explicitly unmeasured until cases occur. The n=5 extension actually took 3.633 s and reached 149 distinct 2B states, yielding 1,192 K premises and 1,192 second-normalized lifts, all passing. None had root v; detached-rho controls remain the root evidence at this stage.

N=6 extension completed in 5.465 s: 179 distinct reached 2B contexts, 3,256 K premises and 3,256 second lifts; zero failures and zero root-v contexts. Together the bounded extensions cover 328 reached contexts and 4,448 K/second-lift cases. The detached-rho root denominator remains four controlled cases only.

Construction followed the adversary phase. ParentTransport.lean and YieldTransport.lean first passed an isolated 21-theorem audit. A final five-lemma SecondCut.lean extension records the exact support and root guard of the second rule; its first standalone compile omitted LEAN_PATH and failed to locate the local import, then compiled with the explicit import path. The final isolated audit checks 26 production lemmas, four named positive control lemmas, nine closed concrete examples and one expected negative compilation. No v1 source changed. REPORT.md states the exact geometry-to-certificate formal interface still open.
