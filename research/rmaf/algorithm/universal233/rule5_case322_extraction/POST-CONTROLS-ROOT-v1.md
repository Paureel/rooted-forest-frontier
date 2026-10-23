# Post-contact root-guard controls v1

Pinned before applying this new guard-completeness control. This is additional
post-contact development evidence; it does not replace the preconstruction pin.

Let T=((a,b),(c,(x,(y,z)))) and U=(((a,(y,(x,z))),c),b).
The literal source frame, proper shared labels and actual target core {a,b}
subtree hold. Its X subtree in T is pendant (one incident arc), so this is
outside the exact Figure15.2 two-outgoing boundary regime. Expected computed
plan: one c-side pendant, no b-side arc after excluding a, LCA(b,c)=root [].
The raw plan's original-AF cover remains meaningful, but its fallback branch
contains [] as an original cut and currentGuard must reject it. Claiming
universal currentGuard from only the raw-cover hypotheses MUST fail.

This plant isolates the extra consuming hypothesis: actual nonpendancy /
exact two outgoing X-hull boundary arcs must imply a nonroot fallback LCA.
No finite failure here refutes the source Case3.2.2 rule.
