# Measured timing and bounded-bank authorization

Plants-v1 and plants-v2 completed first, with known truths, corruptions, empty arithmetic trace and comparator mismatch. ROOT8 pilot0.00146s/50 refiners; pilot4 fixed rows ROOT8 0.00150/50, S8 0.00230/50, S9 0.00548/150, S10 0.01449/450. S11 v2 pilot0.06497/2030. Last two per-refiner costs3.22e-5 and3.20e-5 seconds show no increasing trend at these fixed sizes. Startup/wrapper time is not used as a steady-state rate.

Projection:13650 fixed refiners ×3.22e-5s≈0.440s core checks, plus repeated JSON serialization; conservative launch budget10s. Assumption: comparable block-size distribution across the five explicitly registered symmetry/renaming transforms. Code and settings unchanged from v2 pilot. Real progress is25 completed case rows in bank-v2.json and exact recorded refiner counts. A severalfold slowdown voids this projection; no wider search is authorized by it.
