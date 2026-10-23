# Proper selected-edge C-clearance boundary — v2 frozen before execution

Use S8 source S and parentsP unchanged. Replace target with:
T_overlap=((2,(((0,6),1),(3,7))),(4,5)).
Both original trees have exactly labels0..7; P remains source-valid/source-disjoint. A/B rooted restrictions remain bad; C=(6,7) remains good. The A/B selector should choose edge(0,01), with sectorsAyes01/Ano2/Byes3/Bno45 and valid sector clearances. C's minimal target hull joins6 to7 through01 and overlaps both whole-parent hulls. Thus the selected-edge/source/shape hypotheses hold while C-target-clearance alone fails.

Expected outcome: theorem guard-domain failure for C clearance. Do not infer mandatory runtime refusal from this failed premise. This fills the earlier supplemental's label-mismatch-only boundary, which did not isolate C clearance.
