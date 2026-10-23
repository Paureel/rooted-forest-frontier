# Primitive correspondence interface, concrete stage v1

This stage proves source-level value companions and structural scan/constructor
bills. It does not equate those bills with compiled machine time or bit work.
No Rule5-wide LocalWorkBound field is introduced.

For the common `.one` path, the source bodies are the frozen CallerDefs.mergeCandidates,
RMAF.best and CallerSetup.reconstruct. New checked companions are mergeMeter,
bestMeter, pickMeter and reconstructMeter. Their .value equals the actual body.
The loop proofs charge every original owner occurrence, failed equality/guard,
invalid agreement candidate and duplicate value. They never count just winners.

Let n be leaves(d.T).length and N=2n. Actual closed FastOrdinary.solve marked
callback FM and actual outsideReply FN satisfy cells(FM),cells(FN)<=N.
Every generated checker forest G has cells(G)<=6N+1=12n+1 and
G.length<=2N+1. Those bounds include forests failing agreement. The actual
source build gives rho=inputMax(T,S)+1 and gamma=inputMax(T,S)+2.
Every candidate label <=inputMax(T,S)+2, so L-bit original input labels imply
candidate labels <2^(L+2). No hypothesis about hostile callback payload is used.

The exact checker interface is check : Forest -> Measured Bool, with
(check G).value = RMAF.agreement d.T d.S G and (check G).work<=K
on these literal candidates. The payload and numeric domains above are proved
by common_real_payload, merge_payload and common_real_numeric/common_real_bits.
To instantiate K polynomially, the checker author must supply its actual
agreement (two partitionCheck, all restrictionAgrees, two pairwiseEmbeddings)
source bill on ANY G in this domain, including invalid G. This is a checker
primitive boundary, not an assumed bill for a classifier or whole caller.

Outside agreement, the structural units require these exact primitive scan and
scalar correspondences, with explicit scalar fee rather than unit bit cost:

- X.contains x: <=X.length Nat-equality visits plus one terminal visit.
  filterMeter separately charges each input cell and possible cons allocation.
- Nat-list equality H==B: <=H.length+B.length+1 tag/scalar visits. eraseMeter
  pays every compared B before the first owner equality, and every rebuilt cons.
- swap y rho / swap x gamma: at most two Nat equality tests and a returned Nat;
  relabel pays one scalar call plus a cons per input label and per-block visits.
- List append copies its left spine; merged pays both actual append spines and
  its new outer cons. Neither a forest nor block copy has unit payload cost.
- best pays each checker invocation plus current and RETAINED TAIL forest
  length scans, subtraction, comparison and option/list overhead. It pays failed
  validity checks too. All candidate values are available at these exact sizes.
- reconstruct pays all four input length guards; the unstable branch pays the
  actual FX append, while the stable branch pays the full checked owner scan.

The list/address/scalar fee must cover labels of L+2 bits, counters and budgets
up to the stated n,q bounds, Boolean/option constructors, and copying one list
cell. Pointer model or address bit cost must be stated by the checker model.
scaledWork/reconstruct_scaled multiply the proved structural count by this fee;
they DO NOT assert this fee is a valid machine or bit implementation bound.

The explicit reconstruct structural bound is
  9N + ((8(N+2)^2+2)N+2)N + 7
       + (K+2(2N+2)+2)(|FM| |FN|).
Actual |FM|,|FN|<=N makes this polynomial in n,K. K polynomial in n,L and
the separate scalar fee polynomial in n,q,L give a polynomial local common
merge bill. No recursive ordinary callback work is included in this local bill.

Still open in this stage: admitted/classifiers, source-spine/fork/incidence/
attachments, complete buildSetup/outside pretests, paid.second request and
frontier materialization, forest job check bodies and all other caller paths.
The exact FIRST missing source body is documented in FIRST-GAP-v1.md.
