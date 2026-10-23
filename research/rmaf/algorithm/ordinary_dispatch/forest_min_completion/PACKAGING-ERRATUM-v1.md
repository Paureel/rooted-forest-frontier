# Packaging helper correction

The first freeze helper verified prior content hashes and then requested a
bytes field absent from the older GenericForest v3 manifest. It stopped
with KeyError before creating a manifest or changing permissions. The exact
helper and executed failure log are preserved in results/algorithm-ordinary-dispatch-forest-min-completion-packaging-failure-20261015T144719787490Z.

freeze-v2 retains mandatory exact SHA256 comparison for every prior member
and checks recorded file sizes when that optional field exists. The original
audited helper is preserved unchanged, as are all scientific source/input
pins. This correction changes packaging only; the source/kernel/producer
receipt remains the same. No scientific verification was skipped.
