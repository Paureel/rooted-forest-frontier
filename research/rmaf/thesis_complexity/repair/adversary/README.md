# Independent adversary arm

Status: initialized; no theorem or refutation accepted.

Scope: test the proposed two-active-leaf G4.1 local repair, the protected-sibling-history premise, and the sufficient C-child bound against exact Chapter 2/6 conventions. Read sources one at a time. Root convention: labelled unary rho. Credits and protected edges are distinct. Reachability means the full call tree.

Allowed inputs: source thesis, repair target, proposed lemma, frozen control certificates. Excluded inputs: parent initial Python implementation, review/replay.py, repair_controls.py, and other arms' implementation/plans.

Planned retained artifacts: source-reading ledger, control checks, independent bounded checks, exact witnesses, uncertainty report, and Lean arithmetic receipts.

## Frozen control / independence ledger

Read `repair/controls-frozen.json` before coding. Its five controls are construction/calibration inputs and may never certify a universal theorem. Controls require exact mass 9/16 versus 1/2; dead nine-leaf C; |P|=3, |Q|=2 in thirteen-leaf assignment; live two-leaf C with only B legal; rejection of wrong orientation paired with acceptance of its reverse. Primary code lineage will be fresh and share only source rules, frozen certificates, Python runtime, and basic exact arithmetic.

Toolkit consultation: `bootloops/tools/README.md` has no rooted agreement-forest transition evaluator. A problem-specific, one-shot fresh evaluator is required by the independent-adversary assignment; using or patching the excluded existing implementations would destroy the required lineage separation.

## Source reading ledger — extracted

Whidden thesis local text, printed p12, PDF p25, lines 821–829: "we augment the tree with a labelled root node whose label is distinct from the labels of all leaves and whose only child is the original root"; "suppressing unlabelled nodes with fewer than two children". Thus rho is labelled unary and must survive suppression. Printed p15, PDF p28, lines 932–942 defines yielded forests and edge deletion followed by suppression. No inferred alternative root convention is licensed.

## Candidate under attack

Read `thesis_complexity_review/local-repair.md`; its scope is a current F1 fringe `(a,(x,y))`, protected a plus protected F2 sibling subtree, exactly three x–y pendants, depth(x)>=depth(y), all branches legal, source priority honored. The claim that this forces C dead or B-only with at least three pendant edges remains unverified. History persistence is a separate claim; a locally admissible counterexample without a source history cannot refute the reachable statement.

Whidden printed pp107,109–111: source rules prohibit protected-edge cuts and root-child cuts whose sibling is protected; replacement edges inherit protection. BCY continuation and depth rule were read from rendered PDF p123 / printed p110 (`source-p110.png`), since this page has no text layer. BCY cuts all pendants or the second endpoint plus the protected uncle's sibling. Eligibility is below the deepest parent of an F1 protected edge; deepest eligible sibling pair wins, then separate-component/deepest-member tie break. Printed pp117–126 and rendered PDF p131 / printed p118 (`source-p118.png`) were read for group/credit rules. Source asserts |P|<=2 on p117; this is specifically not assumed. G4 A3BC exception on p123 resets credits in B, retains incoming credits in A, and adds first endpoint to both P,Q in C.

## Executed controls and timing

The first control run failed closed on a local output-path error (retained `thesis-runtime-repair-adversary-controls.log`); no search ran. Corrected the campaign root path; controls v2 passed. Exact five frozen fixtures agree including branch priority and protection sets. The finite evaluator was written from the source, using the certificates as exposed calibration targets; this is fresh implementation evidence, not a held-out validation of the source.

Pilot100: 100 attempts, 21 source-legal local orientations, 31 C orientations, 796 singleton history checks, 0 fires, 0.176726125 s. Pilot1000 (same settings): 1000 attempts, 138 local orientations, 187 C orientations, 7819 singleton history checks, 0 fires, 1.659066750 s. Incremental 900 attempts took 1.482340625 s; at that measured rate 20,000 attempts project to about 33 s under linear scaling. Progress unit is the recorded eligible local orientation count. Next run is bounded to 20,000 with no theorem acceptance from a null result.
