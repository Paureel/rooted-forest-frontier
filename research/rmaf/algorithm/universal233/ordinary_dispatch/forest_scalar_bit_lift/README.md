# Binary reference scalar and checker lift

Import `PolynomialBitBound`, namespace `GenericForest.ScalarBits`.
The finite binary reference providers have exact decode values and concrete
linear work bounds: comparison/equality/order/max, carry addition/increment,
aligned borrow subtraction with saturation, bounded-width addition, bit-array
copy, and binary list-length/index loops. Padding, zero, carry overflow and
borrow chains are included. `encode` proves representation correctness for
values below 2^W; out-of-width controls deliberately demonstrate truncation.

`bitAgrees`, `bitAccepted` and `bitChecked` compose these providers with the
sealed structural checker. Their exact values refine the actual source
checks. The checked reference work is bounded by
256*(L+14+8*labelBits(stateVolume+1))*inspectionBill. For proper states,
`binary_checked_polynomial` gives the concrete bound
256*(L+14+8*labelBits(4*n+q+1))*4096*(4*n+q+1)^8,
where n is the current target-label count. No arbitrary scalar-cost record or
all-budget callback work premise is supplied.

The input label-bit cap L is explicit. `counter_cap_binary` derives finite
binary width for every counter at most 4096*(volume+1)^8. Count checks execute
binary increment, acceptance executes binary length/subtraction/order, and
original hull addresses retain their proved Bool/list scans. `pointerLift`
conservatively expands only the named scalar-free Bool/pointer/copy/address
source sheets. Label equality and scalar count/acceptance operations use the
explicit binary providers instead.

Actual FastOrdinary callback payload size/label premises are discharged from
the completed functional theorem. Literal scheduler/pretest/run assembly
supplies payload labels and sizes before checking. Every raw overlap child
answer and duplicate occurrence is retained. Initial source checks and the
proper guard also receive reference bounds, including malformed rejection.
Rejected small payloads cost nonzero; hostile unbounded payloads remain outside
the semantic payload premise. A callback returning none has no payload check.

The metered scalar bodies are `compareBits`, `addCarry`, `subtractBorrow`,
`alignBits`, `copyBits`, `copiedEqual`, `lengthBits` and `indexBits` plus their
printed wrappers. Their inputs are supplied finite Bool arrays. `encode` and
`decode` are mathematical representation boundaries. The stored `referenceEq`
adapter uses encode to describe represented Nat operands, but its declared
work meters the copied bit-array equality provider. It does NOT meter native
Nat-to-array conversion or establish the compiled runtime of that adapter.
The same cost-semantics qualification applies to the composed checker meter.
The production FastOrdinary program is not rewritten by this release.

Native representation/provider binding, complete compiled runtime/IR
correspondence, the main whole-program bill, fresh-label bit-cap propagation,
base/novelty and independent acceptance remain OPEN. The result is a closed
reference-provider checker cost theorem with explicit source-body scope;
no native or all-imported stored IR cleanliness claim is made.
