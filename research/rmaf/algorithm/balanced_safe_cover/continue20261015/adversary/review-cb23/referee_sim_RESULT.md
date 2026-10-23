# Fresh referee-sim of parent RESULT.md

Scope: CB2/CB3 and their source/formal interfaces. The reviewer authored none
of CB2, CB3 or RESULT.md. The reviewer's own CB1 infinite-family proof is
excluded; its presence in RESULT.md is not independently certified here.
The review uses the completed source bytes and exact reconstruction receipts.

| Audience | Strong standard objection | Axis | Answer location or finding | Severity | Recommended change |
|---|---|---|---|---|---|
| Exact-algorithm theorist | One high-mass finite node does not imply an asymptotic lower bound for the cached solver. | Correctness | RESULT117-121 and157-163 explicitly restrict the failure to the uniform recurrence; new REVIEW explains the mass proof obligation and no runtime guard. | Low | Replace the ambiguous required mass call wording at119 with blocked proof obligation. |
| Exact-algorithm theorist | Are you claiming a new faster exact algorithm from this implementation? | Novelty | Opening3-7 states no unrestricted runtime improvement, and all milestones remain open. No prior-work novelty claim is made. | Low | None. |
| Rooted-forest/source-model expert | Does an abstract CNF example actually arise on the original unsuppressed trees, and does it preserve the intended ordinary convention? | Correctness | RESULT104-115 gives literal trees and edges; independent review reconstructs26 causes, optimum 3 and1024 cutset equivalences. C1 remains open at34-37. Stronger reduction history remains unaudited in the pinned source receipt. | Low | Prefer projected conflict system over reduced conflict system at110 if reduced could be mistaken for a stronger tree-reduction claim. |
| Rooted-forest/source-model expert | Is this a structural novelty claim about ordinary MAF rather than a counterexample to one chosen recurrence? | Novelty | RESULT117-121 and161-163 exclude a general MAF or guarded-cover lower bound. | Low | None. |
| Formal verification reviewer | The literal-profile arithmetic does not extract those profiles from the trees or establish C1. | Correctness | RESULT34-37 and140-142 say exactly that. This review did not replay prior compiler logs and claims no new Lean closure. | Low | Preserve the caveats when adding this finite review. |
| Formal verification reviewer | Are generic list lemmas presented as a new complete solver proof? | Novelty | Opening3-7 and136-142 deny that scope. | Low | None. |
| Solver user | Does the printed optimization wrapper cover the advertised empty input? | Correctness | RESULT63 fails at n=0; actual solve(None,None,-1) raises, while solve(None,None,0) succeeds. | Medium | Use max(0,n-1), or state and handle the nonempty precondition. |
| Solver user | Does the implementation replace the published benchmark? | Novelty | Opening5-7 makes no smaller-runtime claim, and66-67 requires source/correspondence review. | Low | None. |

The title and opening make the open scientific status prominent. The all-row
chapter presents both the exact source witness and its recurrence-only scope
before any broader discussion. The C1 caveat precedes the correctness
argument. Those placements answer the central framing objections where the
relevant readers would look. The empty-wrapper formula and executable-check
wording need the narrow corrections above; neither changes the confirmed
finite obstruction. No literature search or originality claim was attempted.
