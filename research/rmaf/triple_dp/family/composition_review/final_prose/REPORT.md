# Final prose and scope review

Accepted as a narrow checkpoint and next-work specification. No further
required correction was found in the reviewed REPORT.md or NEXT.md. This is
a prose/scope decision against completed evidence, not a new proof or a grade
of full G2. Author sources were not edited.

The reviewed files are retained here as `author_REPORT.md` and `author_NEXT.md`:

| Source | SHA-256 |
|---|---|
| family/REPORT.md | `a92a54e7c2e33fd902e081eb739439047bc4e8ef37858b6c1379d79bf7200abe` |
| family/NEXT.md | `6f907232a0b999e1c76fc9db39f937d648ffe02d1abaae3c38b4fdb8c42ecdd8` |

REPORT:49–51 now states vertex absence and leaves family restriction/charging
separate. REPORT:110–113 now distinguishes zero closed-region cost while open
from the charge upon closing. REPORT:65–75 identifies the concrete transport
functions, normalized rather than original raw supports, and the weaker
existential statement exporting cost and block-count equalities. The opening
and closing status agree with the three completed review records. I also read
fresh_review/REPORT.md: its normalization acceptance, 17 registered control
rows, 31 queried declarations, and three separate reviewer lemmas support the
summary at REPORT:125–128.

The source-level query classification matches REPORT:101–108:

| Cumulative family audit | Theorem queries | Definition queries | Total |
|---|---:|---:|---:|
| Original normalization | 30 | 1 | 31 |
| With geometry | 38 | 1 | 39 |
| With transport and its controls | 47 | 3 | 50 |

The three queried definitions are `normalize`, `toClosedAssembly`, and
`toOpenAssembly`. These are selected axiom-query inventories, not a count of
all declarations in the source files. The rows are nested and cannot be added.
The separate 60 dependency queries are 27 old core/region, 16 path, and 17 cost
queries. All relevant source hashes still match the fresh transport replay.

NEXT:9–21 states merge as an unproved operation with both input boundaries
present. Its proposed block count `L.blockCount + R.blockCount - 1` removes
exactly one of the two distinguished indices; its proposed cost
`L.cost + R.cost` agrees with the existing convention that each child boundary
and the merged parent boundary remain open. The two input boundary hypotheses
ensure their block counts are positive, so natural subtraction does not hide
an empty-family case. The text separates geometric family construction from
color/mask admissibility.

NEXT:25–43 correctly treats restriction at an internal parent node as a new
family construction, rather than an application of the existing pointwise
support identity. It explicitly accounts for a parent closed region becoming
a child boundary and therefore changing the child's cost. The absent/left/
right/both classification matches the four proposed transitions; unused
vertices and empty-fragment exclusion remain explicit. NEXT:53–58 and
REPORT:138–154 preserve the unproved inverse, merge/restriction, graph hull,
color/mask, automaton, and Python interfaces. No novelty or unrestricted
algorithm conclusion is inferred.

I reread the repaired passages, then the two complete Markdown texts for
status consistency, exact costs, query units, and preservation of scope.
This pass did not inspect a rendered PDF/browser export, perform a new Lean
proof, or enlarge a census. The machine-readable record is
`../../../../results/triple-family-final-prose-review.json`.

The previous transport-review report is preserved here as
`transport_review_REPORT_before_terminology.md`, SHA-256
`268f130b8923772c455d752e781eb59b9ae92ec7eb662cfe5fd2a202c47e7f92`.
The live reviewer report now calls the relevant Lean declarations definitions
or functions, rather than Lean constructors. Its corrected SHA-256 is
`1972099834434c14c8c37c5f401f02fd6a0a19e32a7de00534c510cf6b79b533`.
`terminology-amendment.json` records that prose-only change. Historical replay
receipts are preserved, including their earlier classification field names;
this amendment corrects the terminology without changing any executed result.
