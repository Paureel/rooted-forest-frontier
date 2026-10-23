# Source-consumer supplement, version 1

This supplement was pinned after visually reading thesis printed pp.114-115 and before its own X0 or proof construction. It preserves TARGET.md and controls.json. The initial two adversaries were already running and were not steered. The graph adversary must finish its initial pin before receiving this additional exact test.

**CN1.** If a finite input forest has no label-free component, then after cutting C, `components(yield(F-C)) = components(F) + |C| - emptyComponents(F-C)`. Suppression changes no component containing labels; empty components are discarded. This statement includes redundant cuts and rho isolated as a labelled component.

**CN2.** If C is contained in a globally minimum actual-edge cutset K for an acceptance predicate depending only on the yielded labelled forest, then F-C has no empty component. Require attained acceptance and no empty input components explicitly. This claim must be attacked independently before use. Neither an arbitrary C nor minimum among extensions of C suffices.

**RS.** If r is an unlabelled component root of a reduced binary forest with two outgoing edges e1,e2, then cutting e1 or e2 yields the same rooted labelled forest. The subtrees rooted at the two children may be compound. For sequential protection use, prove that whichever child residual edge is cut can instead be replaced by its sibling before lifting, and then choose the designated protected origin on that sibling's original path. Absence of a protected origin on that path is a rejected input, not permission to invent one.

Exact supplement controls, using the original base_graph:

1. C={er}: r is an unlabelled root with children a and s=(b,c). Residual cuts {r-a} and {r-s} both yield component label sets {rho},{a},{b,c}, with the same rooted topology. This is compound-root-sibling equivalence. Total original cut count is two in each case.
2. C={er,ec}: r has children a,b and path P_(r-b)={es,eb}. Cut the residual edge r-a, replace it by sibling r-b, select protected origin eb, and obtain K={er,ec,eb}. Direct K and either residual sibling choice yield {rho},{a},{b},{c}; total cut count is three. The false designated origin ea is outside P_(r-b) and must be rejected.
3. C={er,ea,eb,ec}: raw forest has five components, one label-free ({r,s}), and yield has four. Reject the false value five for yielded component count. C={ec} has two raw and yielded components and zero label-free components.
4. Equal trees T1=T2=rho->((a,b),c) have global minimum zero; a forced set containing the incoming edge of a has forced-extension minimum one. This rejection twin prevents substituting extension-minimum status for global-minimum status in CN2.

The CN2 search must inspect every prefix C of each globally minimum cutset K in its chosen exact finite family, record denominators and stop on any label-free fragment. The RS search must test every unlabelled binary component root in its chosen yielded family, retain topology comparisons, and test the wrong-origin rejection. No initial X0 denominator may be relabelled as evidence for this supplement without the supplementary assertions actually executing.
