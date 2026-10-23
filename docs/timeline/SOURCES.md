# Timeline sources

The README displays the requested ordinary-rooted comparison, with a line from
the reported 2.3391 bound to Paureel's submitted 2.33 bound. Both axes use
logarithmic scales. The x-axis uses calendar document/publication years. The
legend names Paureel's latest project submission; it does not establish a new
best-known result across all public literature.

Confirmed augmented-root entries were removed from the figure at the
maintainer's request. The complete identified source table remains in
[JSON](timeline-data-v1.json) and [CSV](timeline-data-v1.csv), including their
model, output, exponent parameter, read status and publication-date distinctions.
The figure contains three entries:

- **Chen–(Fan)–Wang:** 2.344 as printed in the complete 2012 author manuscript,
  Theorem 7.1 p.30; the file's initial public-posting date is unverified.
  [Author text](http://rnc.r.dendai.ac.jp/ultraNet.pdf).
  The proceedings ebook appeared on 21 May 2013; the conference was held on
  26–28 June 2013. The journal was online in December 2013, issue April 2015.
  [Journal record](https://doi.org/10.1007/s10878-013-9695-8).
  Its abstract also says 2.344; the final body was not retrieved. The later
  Split-or-decompose text attributes 2.3431 to this earlier algorithm.
  The 2012 text has no explicit rho, while calling its optimum rSPR; the
  historical final-body convention/version comparison remains incomplete.
- **Mestel–Chaplick–Kelk–Meuwese:** ordinary rooted O*(2.3391^K),
  Theorem 17 p.26, with conventions in section 2 p.4, footnote 2.
  [Split-or-decompose v2](https://arxiv.org/abs/2409.18634v2).
  First preprint: 27 September 2024; v2: 21 March 2026. The final JCSS
  journal metadata is September 2026; its body was not separately compared.
- **Paureel:** submitted mathematical O*(2.33^K) proof for ordinary rooted MAF.
  [Proof and verification limits](../../expert-review/20261023-v1/PROOF.md).
  The earlier qualified internal acceptance, shared formal support and external
  review limits remain unchanged. The project date does not establish public
  priority or certify a particular native executable.

The separate prior-art assessment on 23 October 2026 did **not clear an
unqualified best-known claim**. Whidden's public 2013 thesis contains an
O(2^q n) algorithm and substantial written correctness/cost proofs for its
augmented-root model; it was not independently validated or refuted in that
assessment. Dempsey's 2021 thesis gives an O(2.27^k n) core-MAF algorithm,
parameterized by usual augmented MAF size. Exact transfer to the ordinary target
remains undetermined in the inspected sources. Relevant TCBB 2020 and full
Meuwese 2025 texts, among other access/version checks, remain unread. Removing
those entries from a selected plot does not remove them from the comparison.

Primary thesis records:
[Whidden 2013](https://dal.scholaris.ca/items/1544e972-7fb4-42d7-b87d-b1e78b6ab9b6),
[Dempsey 2021](https://dalspace.library.dal.ca/items/ca256e10-5d53-4c40-a3c0-3935f7880017).
The full per-source fields and URLs are retained in the table. A source proof
being read is distinct from independent mathematical verification.

The SVG is text rather than a binary image, consistent with the repository's
file policy. The local PNG preview is not committed. To regenerate both images,
run `python render_timeline.py` in this directory with Matplotlib installed.
The renderer is a one-off presentation script; it performs no search, fitting,
recurrence calculation, or solver computation. All research and monitoring
remain paused.
