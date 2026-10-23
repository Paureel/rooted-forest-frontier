# Correction to the axiom-summary journal note

The immediately preceding REVIEW axiom-summary paragraph and the scope string in AXIOM-INVENTORY-SCOPE-v1.json are incorrect. The author manifest, author certificate and fresh full stored audit all list the same three standard axioms: Classical.choice, Quot.sound and propext.

Cause: the initial manifest metadata display deliberately sliced every list to its first2 elements. I later treated that display as the full standard_axioms field. Reading the complete field in the executed comparison exposed the error. The v1 file already carries the correct three complete lists; only its explanatory scope string and the journal paragraph were wrong. Both remain preserved and are superseded here.

No acceptance rule, source pin, declaration count or dependency result changed. All three standard axioms were allowed before candidate contact, and the full stored audit rejected zero declarations. AXIOM-INVENTORY-SCOPE-v2.json records the actual agreement.
