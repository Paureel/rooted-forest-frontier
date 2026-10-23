# Runtime representation and elementary implementation

The input domain is exactly the canonical finite binary datatype `Tree = Leaf(Nat) | Node(Tree,Tree)`. A leaf is a one-label tree; a node has exactly two children. There is no added root, sentinel label, degree-two normalization promise or supplied properness evidence. Paths are lists of Boolean left/right steps. Labels are nonnegative integers. Malformed ordinary pairs means the actual computed proper predicate is false, including repeated labels or different leaf-label multisets; QUERY returns None and OPTIMIZE retains no trials/recoveries. The optimization parameter k is minimum COMPONENTS among agreeing common forests, and the query cut budget is q=k-1.

Use the unchanged natural-word log-cost operation convention of MODEL-v2/COST-v2, with32 architectural registers and immutable fresh heap appends. This mathematical implementation has its own finite procedure bodies and activation records; it does not claim to execute the earlier numeric listing. It may use ordinary registers for local arithmetic and typed immutable heap records for spilled locals and pending continuations. The paid decoder below reads the exact previously specified raw word; the old encoder certificate is optional supporting evidence, not an assumed certificate for this different whole program.

## Exact raw words and paid decoder

Retain PUBLIC-RAW-INPUT-v1's mathematical code. For each label x, let bin(x) have max(1,bitLength(x)) digits, most significant first, and natfield(x) be that many1 digits, then0, then bin(x). In low-to-high consumption order a LEAF token has digits0,0; NODE1,0; END0,1; tag1,1 is invalid. Define post(Leaf x)=LEAF++natfield(x), post(Node l r)=post(l)++post(r)++NODE. With bits=post(T)++END++post(S)++END of length B and digits b_i, the actual input word is U=2^B+sum(b_i*2^i). These powers define the input's contents; no exponentiation is a runtime input operation. Initially U is in r8,q in r4,all other registers0,heap empty. The new mathematical program starts at its fixed DECODE entry. There is no source Tree/parse tree/heap result supplied for free.

The following is the new implementation's elementary decoder, using a paid heap list stack rather than silently importing any old machine certificate. Allocate nil at0. Save q by COPY; no width is supplied. Every digit read tests U>1 then LOWBIT and SHR1 on the full actual unread word. Every stack test/head/tail access and constructor is a paid operation with the layouts below.

```text
READ_DIGIT():
    if U<=1: fault truncated
    b:=LOWBIT(U); U:=SHR1(U); return b
DECODE(U,q):
    emit canonical nil0; stack:=[]; phase:=0
    loop:
      b0:=READ_DIGIT(); b1:=READ_DIGIT(); tag:=b0+SHL1(b1)
      if tag=0:                             // leaf
        width:=0
        while READ_DIGIT()=1: width:=width+1
        if width=0: fault badNat
        x:=READ_DIGIT()
        if width>1 and x=0: fault badNat
        remaining:=sub(width,1)
        while remaining!=0:
            bit:=READ_DIGIT(); x:=SHL1(x)+bit; remaining:=sub(remaining,1)
        root:=fresh Leaf(x); stack:=fresh cons(root,stack)
      else if tag=1:                        // node, right popped first
        if stack=[]: fault stack
        right:=head(stack); stack:=tail(stack)
        if stack=[]: fault stack
        left:=head(stack); stack:=tail(stack)
        root:=fresh Node(left,right); stack:=fresh cons(root,stack)
      else if tag=2:
        if stack=[] or tail(stack)!=[] or phase>=2: fault treeBoundary
        root:=head(stack); stack:=[]
        if phase=0: T:=root; phase:=1
        else:
            S:=root; phase:=2
            if U!=1: fault trailing
            return (T,S,q)
      else: fault badTag
```

Node/leaf records and interleaved stack cells are real fresh allocations; popped stack cells remain allocated. All loop counters/arithmetic and copies are paid. No arbitrary shift or width opcode is used. For actual codes, a postorder forest invariant proves that the stack lists exactly completed source subtrees, each NODE combines its last two, each END finds one tree, canonical label fields recover every natural including0, and the final sentinel is1. Each read consumes a real digit; the header/payload loops and token loop terminate on the finite encoded word. Invalid raw words take an explicit fault, without an added arbitrary corrupted-heap theorem. These direct parsing invariants are the mathematical decoder proof obligation for this implementation, not a transfer of a numeric listing result.

Writing n=nT+nS and J=sum of label widths over all occurrences, B=5n+2J and w(U)=B+1. Thus for nT,nS<=N,label widths<=L, `w(U)<=10N+4NL+1`; q<=Q bounds its separately charged input word. These bounds are analysis parameters only. Postorder constructors total2n-2; leaf/node heap words plus nil total5n-5; the immutable stack adds3(2n-2) words. The label/stack/control copies are charged on their actual current widths. The local/global cost proof must include this actual initialization prefix and all its addresses.

Heap address0 is the canonical nil word, allocated and written initially. A cons is a fresh block `[1,head,tail]`, Leaf a fresh `[2,label]`, Node a fresh `[3,left,right]`. Product/record fields are a fixed ordered sequence of cons cells, final tail0. A constructor tag is the first record field, followed by its retained computational fields. None is0; Some(v) is the two-field record `(1,v)`. Boolean words are0/1. Tree/path/forest references are addresses of the actual allocated start. Nested products retain their nesting, e.g. `(path,a,b)` means `(path,(a,b))` where that is the actual source product type. There is no reference equality shortcut for structural equality.

CommonForest is List(List Nat). Candidate retains parent,a,b,originalCuts. RawChoice retains a,b,c,cHead,xHead. Early and Front use the tags and field order in ALGORITHM. Setup retains its exact16 computational fields, LiteralGeometry its exact13, and SelectedPaid its declared computational fields. Colored trees, Paint/Local/Colors, children, outputs, jobs, modes and all receipts use the exact field orders/types printed in the appendix, after only the named projection. Strings are the seven fixed recovery refusal literals printed in CoreProgram; encode them by distinct fixed codes in source order and retain actual refusal lists. No arbitrary String processing is needed at a reached consumer.

All data is immutable. Copying a reference is a paid word copy and shares its immutable target. Constructing a list copies exactly the requested spine; append copies the first spine and shares the second. Tree constructors share already computed children; tree traversal/relabel/restrict explicitly allocates the nodes the body constructs. No automatic deep copy, memoization, hash-consing, cached length, deduplication or GC is supplied. Every source repeat that remains in a decision/value/retained diagnostic is a fresh traversal or computation at that position.

## Procedure control, storage and finite constants

A procedure call is implemented by a finite continuation tag plus a fresh immutable activation record containing the previous frame reference and each actual live local/argument needed after return. Argument loads, field-address additions, saved copies, all record words and return decoding/dispatch are paid. A loop is an ordinary conditional/backedge with paid counter/pointer changes. A recursive list/tree routine can use these frames; it does not use an uncharged host stack. Every continuation denotes one fixed lexical callsite of this finite pseudocode, never an input program, expression tree or answer procedure. The initial activation is also paid.

Use the following explicit conservative constants for cost assembly. Let S be the sum of UTF-8 byte lengths of the frozen main pseudocode, literal procedure appendix, all five computation DATA files (constructor,Rule4,properness,agreement,tree) and this representation/projection specification; S is printed as a static identity size in the manifest, not computed by the runtime. Assign each syntactic argument, named local, pattern binder and temporary expression result one fixed slot at its own lexical occurrence. There are at most2S+16 slots in any activation, since each occurrence occupies at least one byte and the extra16 holds previous frame,return tag and control temporaries. Thus fix `Fmax=2S+16` as a uniform frame-size upper bound. Allocate only the fields actually used by that activation, with no padding. The number of fixed lexical callsites is at most S; fix `Kmax=S+1` as a return-tag/dispatch upper bound. A callsite may be identified by its source-view/declaration/line/lexical occurrence from SOURCE-INDEX; these are fixed program constants. They are not runtime oracles. The local-cost owner may tighten these deliberately loose finite constants by counting the displayed bodies.

Finite return dispatch uses a literal comparison chain against fixed natural tags, followed by direct branches. It costs at most Kmax comparisons/branches and their literal preparation; invalid tags fault. A native instruction address, arbitrary function pointer or type-start operation is not an input. Lists of finite thunks contain a tag plus a real environment of their captured fields. All environments and lists are allocated before evaluation at the places specified by the bodies. Thunks have only the finite target specializations listed by the implementation, including the17 literal predicates and their nested OR arm. No generic source interpreter is executed.

## Elementary operations and local contracts

Write `w(n)=max(1,bitLength(n))`. For actual pre-state operands x,y, result z, address u, pre-heap bound m and post-bound m', successful fees are:

|Operation|Charge|
|---|---|
|CONST c|1+w(c)|
|COPY x|1+2w(x)|
|ADD / truncated SUB x,y|1+w(x)+w(y)+w(z)|
|SHL1 / SHR1 / LOWBIT x|1+w(x)+w(z)|
|EQ / LT / LE x,y|2+w(x)+w(y)|
|BNOT x|2+w(x)|
|BAND / BOR / BXOR x,y|2+w(x)+w(y)|
|conditional branch b|1+w(b)|
|direct jump / halt|1|
|READ u|1+w(u)+w(m)+2w(z)|
|WRITE u,v|1+w(u)+w(m)+2w(v)+w(m')|

Fault fees and all previous charges are retained exactly as COST-v2; no no-fault result is assumed. Aliased/repeated operands pay each pre-state occurrence. Every successful word emission is WRITE at actual next address m, CONST1, ADD nextAddress,1; value/tag preparation is separate. Its fee is `5+3w(m)+2w(v)+2w(m+1)`. A cons executes three such emissions plus pointer/tag preparation; a field read executes paid constant-offset preparation, ADD and READ. A record projection walks actual tail links, so a field at index j requires j tail reads and one head read, with paid offset arithmetic for each.

The following are elementary implementations, not constant-time library assumptions. Their operation-count recurrences count elementary operations plus their explicitly invoked callbacks/activation handling. The mathematical bill is the sum of actual fees above. No row assumes the desired bound A(C+1).

|Primitive|Concrete implementation and size/work contract|
|---|---|
|length, isEmpty, headOption, headD|length initializes pointer/counter/0/1/2, loops EQ/BR, ADD address by2,READ tail,ADD counter1,JMP. This is at most7n+8 elementary operations for n cons cells, excluding its paid call/return. No heap result record is needed for the Nat. isEmpty is EQreference0; headOption/headD branch then READ head and construct Some/default only when the source body does. Length's discarded source meter work is irrelevant to this traversal's actual charge.|
|cons / leaf / node / fixed record|Emit each word freshly as above. A cons needs3 writes, Leaf2, Node3. With source head/tail words ready, a cons uses at most12 elementary operations; pack r fields uses r such cons constructions plus the finalnil constant. Record field loads and input preparation are additional paid operations.|
|append / map / filter / filterMap / flatMap|Use the exact recursive body. At each cons test nil,READ head/tail,run the fixed head predicate/map and recursive tail in the written order,then allocate the selected result cells. Append copies each first-spine cell once; flatMap additionally performs append on each actual head result, including duplicates. Every callback has paid activation overhead. A tail-first body remains tail first.|
|all/any/find/checks|Use the appendix's particular eager or short-circuit body, never a generic replacement. Eager all/filter evaluates current then full tail even on false. LiteralAtoms all/any and first/find stop at their written first deciding result. Constructed later predicate environments remain paid even when not invoked.|
|contains/erase/nodup/perm/count|Traverse the written spine with actual structural equality. Nat equality uses EQ. Erase stops at first hit and copies its reached prefix. Count traverses the whole tail. The ordinary properness version eagerly contains,erases and recurses even after containment false; distinct short-circuit Rule5 versions retain their own bodies.|
|take/drop/index/reverse/flatten|EQcounter0/nil,READ cells,decrement by truncated SUB1; take copies reached prefix,drop shares reached suffix,index returns actual option. Reverse conses each head to an accumulator. Flatten executes its literal recursion and append lengths, not a unit flatten operation.|
|tree/path/product/list equality|Compare constructors and retained fields with EQ/Boolean control; recursively compare fields in the named body's order, using real traversals rather than pointer equality. SameShape intentionally evaluates all four node pairings before its Boolean combination; LiteralAtoms tree equality short-circuits as printed.|
|leaves/subtree/restrict/rooted/minimal/pendant|Use the actual recursive bodies and allocated prefix path/list/tree constructors in the appendix. Subtree consumes one Boolean path cell at a time. Restrict invokes contains at each leaf and constructs the retained restricted tree. Hull/pendant computations do all their written repeated rooted/minimal/prefix/contains traversals.|
|max/min/sum/component cost|LE/BR/COPY or ADD and actual list traversal. additionalCost=truncated(length(F)-length(ss)); sourceCuts.length, partition.length, knownCost,pending,allocated and answerCost remain actual traversals/arithmetic where written.|
|multiplication|There is no multiplication opcode. Fixed literal products use the literal binary SHL1/ADD expansion. Variable x*y uses accumulator0; while y!=0, test LOWBIT y,ADD x if set,SHL1 x,SHR1 y. At most w(initial y) iterations, each a fixed number of paid comparisons,branches,shifts/additions. Intermediate/result widths are actual operands for the global width proof.|
|arrays/fixed tuples|The implementation uses immutable fixed tuples and lists. A fixed-offset field is CONSToffset,ADDbase,READ. A built finite table is emitted word by word. No high-level mutable array update, bulk allocation/copy or resizable vector primitive is assumed. The DP body uses its displayed finite colors/trees/lists; any table rendering is a sequence of these actual operations.|
|budget/control arithmetic|All guards use actual retained Nat values; subtraction is truncated. Every loop branch, refusal test, callback cutoff, q comparison, success option test and return dispatch is paid even if it emits no answer.|

Each high-level body is realized by expanding these fixed operations and finite control contexts. The expansion is justified mathematically on this finite code, not by supplying a universal evaluator. The per-procedure count is obtained by adding its displayed fixed operations, actual traversals/constructors and each reached child count, including failed/duplicate branches and retained diagnostics. Each atomic fee is then bounded only after deriving the actual operand/result/address-width envelopes. The separate local-cost proof must print the resulting polynomial credit, the global proof must derive space/address/label bounds, and only then may the SOURCE counter bound be joined to obtain O*(2.33^k). Those proofs and their acceptance are not asserted by this specification.
