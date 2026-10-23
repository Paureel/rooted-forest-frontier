# Elementary realization of the frozen cons-record pseudocode

This is a constructive mathematical L3/L5 lemma under TARGET-v3. It uses the
frozen `REPRESENTATION-AND-OPERATIONS-v1.md` and `PROJECTION-v1.md` licensed by
root release `5d10f25e…`, with the additive active projection amendment v2
licensed by `2bbc46e4…`. It supplies a finite realization factor after the
abstract operation count U0. It does not prove that count, its source-occurrence
correspondence, the global semantic width catalogue, input setup, or the whole
solver bound. The unchanged model is `WordRAMV2.lean`: 32 natural-word
registers, fresh word appends, the listed unary/binary operations, read/write,
Boolean branch and direct jump. Its cost is 1 plus the widths of the actual
footprint values, at most five values. No multiplication, allocation, bulk
copy, host record or host stack opcode is added.

## Statement and finite constants

Let f>=3 bound the number of logical fields in each fixed record and activation,
including its actual control fields, and let c>=1 bound the finite call-target
and continuation-tag variants. An operation counted in U0 is one fixed-record
constructor/projection/copy, assignment, elementary scalar call, branch,
activation call, or activation return. Calls and returns are separate counted
control operations; a scalar helper's direct entry and paid return may instead
be covered together by its one scalar-call bound.
Scalar calls have at most two scalar operands; a division result has two words.
All value-dependent list/tree/generator/callback visits, structural equality,
deep copy and power iterations remain separate counted operations. Nested
records retain their actual nesting. Each intermediate expression result has
its own finite activation slot; compound expressions are split at these counted
operations. This is the U0 convention before the realization factor.

Define

```
R = 3f+4,
P = f(R+12)+2 = 3f^2+16f+2,
F(f,c) = 9f,
gamma(f,c) = 9f^2+63f+3c+62.
```

There is a direct finite expansion of these operations with at most F fresh
words per operation. From a valid initial heap of H0 words, at every prefix
`H <= H0 + F*U0`, where a started operation is counted. This allocation bound
has no operand-width premise. If B>=1 bounds the actual semantic operand and
retained field/tag widths and all valid read/write/allocation frontiers, including
the end of each fixed allocation, each operation takes at most
`gamma*(B+1)` primitive instructions. Every actual footprint word then has width
at most `2B+3`, and its unchanged-model bill is at most
`16*gamma*(B+1)^2`. Partial operations satisfy the same upper bounds.

The width premise concerns actual reachable boundaries and addresses, rather
than only the initial input. The allocation conclusion is established first;
the separate global join uses it to derive address widths without assuming an
instruction count. Persisted scalar results belong to the separate semantic
catalogue. This lemma does not infer that a product has the width of its inputs.

The frozen manifest gives S=367507, f=2S+16=735030,
`3f=2205090` words per largest pack, and c=S+1=367508. These are deliberately
loose finite syntax bounds: an argument/local/binder/temporary occupies a
lexical occurrence, with the extra 16 slots for controls. Fixed constructor
arities fit this bound as well. There are at most S lexical callsites and one
initial continuation. Finite callback-target specializations are lexical
occurrences as well and have at most S variants. The helper frames need at most the reserved
control slots. Therefore this implementation has

```
F = 6615270,
gamma = 4862469317576.
```

The manifest's 2205090 is a per-pack word bound; F permits three packs. None of
these constants is a source work count, a local credit K0, or a runtime input.
The active amendment deletes exactly Built.coloring and InitialMeasured.coloring
in RWInitial and unboxes their remaining single-value wrappers. It adds no
procedure or callsite. Therefore f/c remain conservative bounds; the expansion
uses the smaller actual arities. No equality of old and new heap addresses or
fees is inferred from that deletion. Source-consumer preservation is a separate
projection obligation; this lemma uses its explicitly stated active layouts.

## Actual record and activation recipes

Nil is the already allocated word 0 at address 0. Cons is `[1,head,tail]`, Leaf
is `[2,label]`, and Node is `[3,left,right]`. A logical fixed record is exactly
the specified sequence of cons cells ending in 0; its constructor tag is the
first logical field. No field layout is flattened. The expansion at a fixed
lexical constructor uses its actual arity r<=f, without padding.

Keep the next fresh address HP in one register. To emit a ready word v execute
`WRITE HP,v; CONST one,1; ADD HP,HP,one`. Each WRITE is at the actual memory
length. Cons uses three such emissions, a saved starting pointer, the tag
constant 1 and the resulting tail/root copy: at most 12 instructions with ready
head/tail words. Leaf and Node fit the same bound. There is no mutable heap
write and no allocation opcode hidden in this recipe.

To project logical field j, copy the record pointer into cursor; repeat j times
`CONST offset,2; ADD address,cursor,offset; READ cursor,address`; finally use
offset 1 and READ its head. This is `1+3j+3 <= R` instructions. The field index
is fixed by this lexical use; the repeated tail walks are actual reads, not a
base+j shortcut. An explicitly projected single-value wrapper is only a paid
copy. To pack/copy an r-field record, start tail=0, obtain each next head in
reverse field order from an existing activation/record by at most R instructions
(or a ready word/constant), then cons it onto tail. End with a root copy. The
bound is `r(R+12)+2 <= P` instructions and exactly 3r fresh words. References
are shared; variable-size spines and subtrees are constructed by their separately
counted visits.

All source values live across a call reside in the actual immutable activation.
The current activation pointer and HP stay in two architectural registers.
An assignment builds a new activation version with the same previous-frame and
return-tag fields and its one changed slot; old versions remain allocated.
A call packs the callee's actual argument/local/control fields, a reference to
the current caller activation and the lexical continuation tag, then changes
the current pointer. A finite callback call first decodes its fixed target tag
by a literal comparison chain of at most 3c instructions; direct calls need no
such chain. Its body and eventual return are separately counted. A return
projects its caller reference/tag and result,
builds the caller's new activation with that result slot, restores the current
pointer and follows a finite literal comparison chain. Tags 1..c require at
most `CONST tag; EQ; BR` for each tested tag, hence at most 3c instructions.
Only the prefix through the actual tag is executed; an invalid tag faults.
There is no computed instruction address or input continuation procedure. The
initial continuation exits directly without projecting a caller from nil.

An arithmetic helper saves the caller by one fixed, unpadded activation containing
its actual control fields; arguments/results are register words. Its body makes
no child calls. The caller's other live values already reside in the saved
immutable activation. No dead arithmetic scratch is saved as a semantic field.
If a two-word result needs a record, that record is paid. At most three packs
cover any one administrative expansion: a result record, a callee/helper
activation and a new caller activation. Bodies of called procedures contribute
their own U0 operations. Thus allocation is at most `3*3f=F`, independently
of bit widths. A scalar operation needs at most two operand projections and
three return-control/result projections outside these packs: at most 5R.
Reserve three entrance instructions (copy the source base, install the callee
root, jump), three result instructions (two scalar result copies and select
the result root), three restoration instructions (copy the caller base, install
its new activation root, jump), and three branch/exit instructions (EQ to zero,
Boolean branch, jump). Thus at most 12 routing instructions suffice; operations
do not need all four groups. Record field preparation is already in P, and
the one target-or-return decoding chain is already in 3c. A scalar helper has
a direct fixed entry and only its return needs decoding.
For non-helper operations, unused packs/projections/routing only decrease this
bound. Packing each field is sequential, so no f-register tuple is needed.
Registers 0/1 hold HP/current frame. Registers 2..12 suffice for source/caller
bases, construction tail, head, cursor, address, one, offset, root, tag and
condition. The scalar body uses at most registers 13..28. This fits within the
32 registers and leaves HP/current frame intact during each scalar loop.

These recipes preserve the representation at every public operation boundary
by induction. Old cells never change; fresh cells are disjoint. During an
emission HP equals the new length after its final ADD (and is one behind it
between WRITE and ADD); every subsequent WRITE again uses the true end.
A new object pointer is exposed only when its whole record is complete.
Its fields refer to already complete immutable objects or scalar values.
The stored caller reference gives a well-bracketed continuation chain, and
return uses that very reference. A partial new pack is private construction
storage. Popped frames, duplicates and failed/refused attempts that were
constructed remain allocated. These invariants prove both safe accesses and
the prefix allocation inequality; they assume no supplied successful trace.

## Allocation-free scalar scans

One-word ADD, truncated SUB, comparison, Boolean operation or unit shift is an
actual model primitive. Tests produce valid 0/1 branch operands. Comparisons
and short Boolean routing use the same paid operations. Variable multiply
uses the following register recurrence:

```
a=x; q=y; z=0
while q!=0:
    b=LOWBIT(q)
    if b: z=z+a
    a=SHL1(a); q=SHR1(q)
return z
```

After t iterations, `a=x*2^t`, `q=floor(y/2^t)` and
`z=x*(y mod 2^t)`, so `z+a*q=x*y`. There are at most B iterations. Four setup
instructions, at most 8 per iteration, the final test and exit jump give
`8B+7`. If x,y<2^B, both z and even the final shifted a are <2^(2B).
Only registers change inside this loop. Concretely an iteration uses EQ/BR
for q=0, LOWBIT/BR for its bit, optional ADD, SHL1, SHR1 and the back jump.

For division, if d=0 return `(0,x)`, matching Nat division/modulo at 0, in at
most 10 body instructions. Otherwise reverse x's bits into a register rev and
count their number n. This takes at most 8 instructions per bit: EQ, BR,
LOWBIT, SHL1, ADD, SHR1, counter ADD and jump. Process exactly
n low bits of rev, including leading 0 bits: set `r=2r+bit`, `q=2q`; if d<=r,
set `r=r-d; q=q+1`; decrement n. The second phase executes EQ, BR, LOWBIT,
SHR1, SHL1, ADD, SHL1, LE, BR, optional SUB/ADD, counter SUB and jump: at most
13 instructions per bit. Including setup/final tests/jump the body has at most `21B+14`
instructions. At each second-phase boundary the processed input prefix equals
`q*d+r`, with `0<=r<d`; this proves quotient/remainder. The temporary remainder
is <2d, and reversal/quotient use at most B bits. The bit-count register is at
most B, whose word width is at most B for B>=1.

Bitlength copies x, initializes a counter 0, then repeatedly SHR1s the copy and
increments the counter until zero: at most `5B+8` instructions. It returns 0
on x=0. The model width `max(1,bitlength)` adds at most 3 instructions if a
runtime consumer actually requests it. Division and bitlength are available
only at their scalar uses; including them here does not hide any source loop.
All these body bounds are at most `24(B+1)`, using only registers and the one
paid helper frame outside their bit loops. No heap cell is allocated per bit.

## Instructions, widths and unchanged charges

For an operation the preceding explicit bounds sum to

```
3P + 5R + 3c + 12 + 24(B+1)
 = 9f^2+63f+3c+38 + 24(B+1)
 <= (9f^2+63f+3c+62)(B+1).
```

The semantic and frontier widths in the statement bound every loaded/stored
field and actual memory length. Cons field addresses use offsets 1 or 2 inside
real allocated cells. Dispatch tests tags in increasing order and stops at the
stored tag t; every reached comparison literal is <=t. Small constants, Boolean
results and loop counts fit `2B+3`. ADD/SHL temporaries require at most B+1
bits; multiplication requires at most 2B, and division/reversal/bitlength obey
the bounds proved above. Thus every actual footprint value, including repeated
read/write values, old/new memory lengths and allocation addresses, has width
at most `2B+3`. No fee is inferred from a desired run or annotation.

Each instruction therefore costs at most `1+5(2B+3)=10B+16<=16(B+1)`.
Multiplying the actual instruction count gives `16gamma(B+1)^2` per operation.
The root join may multiply this gamma once after its separate
U0/K0 bound. Input setup I/H0, exact projected source occurrences, LocalU0
credit, and the global boundary width catalogue remain separate obligations.


[The following author execution/control outcomes are omitted from this argument-only copy. No independent acceptance is conveyed by this argument.]
