# Exact Rule5 earlierClear consumer v1

Read source: frozen functional package, `Rule5Defs.lean:5-6` and `:23-29`.
The literal admitted let consumes `Rule5Local.earlierClear T S` and its reverse:

    def earlierClear (T S : Tree) : Bool :=
      (candidates T S).all fun c => c.originalCuts.length == 2

Existing own proved interface (`PendantCandidates.lean`) is:

    earlier_value (T S) : (earlierMeter T S).value = Rule5Local.earlierClear T S
    earlier_work (T S) : (earlierMeter T S).work ≤
      earlierBudget (leaves T).length (leaves S).length

The concrete structural polynomial is
`candidatesBudget nt ns + (2*ns+2)*nt + 2`.
It applies also to failed scans, duplicate labels and missing endpoints; no
proper-pair hypothesis is assumed. `AdmittedWork.admittedGuards` uses these
literal guards at positions 3 and 4, after the strict partition let and two
previous short-circuit guards. This is an internal value/source bill, not a
meter for `CherryBranching.select` or `Rule4.select`.

External early-selector integration remains a root-supplied frozen interface:
its actual value companion must equal the exact primitive select body; the
work envelope must expose structural/cell/scalar units and domains. No desired
whole Rule5 local-work conclusion may be imported as an interface premise.
No primitive selector metering is implemented or read from the live sibling.
