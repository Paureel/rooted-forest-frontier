# Superseded audit

The certificate in this directory is retained as historical evidence and does not establish three false-proposition detections. Its FalseSuppressParent entry was accepted because the old parser permitted any failure containing the word `failed`. Lean actually failed to synthesize a Decidable instance for Adj. A true-edge example with the same `by decide` tactic failed identically. The fresh reviewer identified and demonstrated this defect.

The current control unfolds Adj before decide and has a matching clean true-edge control. The current audit parser requires Lean's explicit diagnostic `proved that the proposition ... is false`; generic elaboration or synthesis failures cannot count. The current certificate is ../certificate.json. The main graph proofs and their axiom inventories were unaffected; current sources were rebuilt after the correction.
