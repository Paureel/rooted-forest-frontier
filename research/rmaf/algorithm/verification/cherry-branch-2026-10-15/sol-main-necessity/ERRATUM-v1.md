# Preserved prerelease failures

## 1. Cut list order assumption, controls run1

The fresh graph instrument produced the correct t2 pendant set {01,001} in parent-scan order, while the manually listed expectations used child-address preorder {001,01}. `graph-controls-run1.log` preserves the exact failure. Public controls specify sets/priority and root TARGET explicitly says to freeze actual order only where specified. No actual cut order was specified. This is an overstrong comparator, not a mathematical counterexample. Keep literal expectations unchanged; v2 compares the frozen cut sets and retains its actual list order in readouts. No candidate had been contacted.

The pilot was inadvertently launched in the same tool invocation before the controls log was inspected. Its preserved run1 output is exploratory and invalid for the planned gate sequence. No pilot scientific pass is credited. Restart the gate at planted controls after repairing only this comparator, then use a fresh named pilot. Both failure artifacts and the original script are preserved.
