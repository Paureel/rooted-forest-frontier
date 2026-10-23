# Measured compute plan

The n=4 narrowed pilot processed 500 AF cutsets in 0.05864 s. Its steady window from 100 to 500 cutsets took 0.04365 s (about 9,165 AF cutsets/s); later windows did not slow down. It had started 3 of the 225 tree pairs. A rough same-regime pair-count projection is 4.4 s; difficulty varies by pair, so this is only a planning estimate. The exhaustive n=4 family contains at most 225×3×128=86,400 raw cutsets before any prefilter. The next run is the complete same n=4 enumerator, expected well below a minute; it reports exact counted premises rather than a coverage percentage.

The n=5 pilot uses the same code on the new regime and is measured separately: 500 AF cutsets in 0.04466 s. That first pair happened to have no compound-sibling premises, so it is not claimed representative of compound cases. The follow-on run is bounded to 20,000 AF cutsets, with the same seeded pair order, and will report its actual compound and boundary denominators. No larger unbounded n=5 run is planned. Measured pilot scaling predicts seconds, not a long job; a slowdown invalidates that estimate.

These are wall-clock planning observations, not algorithmic runtime claims.
