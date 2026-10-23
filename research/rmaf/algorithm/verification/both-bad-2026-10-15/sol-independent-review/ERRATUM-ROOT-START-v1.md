# Exact root-start erratum v1 — frozen before engine execution

Date: 2026-10-15. Basis: TARGET-v1 starting fixture and public capsule PUBLIC-DEFINITIONS-v1.json, especially Selector.lean original lines531–560; no candidate source contact and no graph engine has run.

The proposed starting tree is not in the requested selected-edge regime. It remains an original both-bad/rooted-good/source-disjoint boundary control with the stated 5-block AF witness.

At target vertex00, both parent hulls contain00. B={3,4,5} occupies three components after deleting00: label3 below child000 (region0), label4 below child001 (region1), label5 in the parent direction through0→01 (region2). Hence vertexOK(T,A,B,00)=true. Vertex[] is in neither minimal parent hull. Vertex0 is in both hulls, but each parent occupies only its two child components and has no label in the parent direction, so vertexOK at0 is false. The public preorder vertices list is [],0,00,..., so actual choose(T,A,B)=some(vertex00).

Moreover edge(00,000) has the asserted endpoint graph degrees but fails the public edgeOK clearance condition: A_inside={0,1} has a minimal target hull containing000 and0000; both vertices belong to the whole B hull. Thus A_inside hull is not disjoint from B. The opposite B_outside={4,5} hull includes00, also in whole A hull. Graph endpoint degrees alone do not establish edgeOK.

Correction: retain the root literal as an exact vertex-selector/clearance boundary control. Do not call it an in-regime production selected-edge fixture. Construct a new selected-edge fixture from public mathematical definitions, freeze its literal expectations separately, then test it with the fresh engine. The abstract paid trace examples remain independent arithmetic controls and are not changed.

This is a hand derivation awaiting an executed exact confirmation. If an engine disagrees, stop and diagnose; do not edit these expectations to fit it. No frozen root file is edited.
