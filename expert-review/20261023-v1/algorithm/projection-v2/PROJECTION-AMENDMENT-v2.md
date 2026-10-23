# Additive recovery projection amendment v2

Apply this amendment to the frozen math_pseudocode_v1 package, manifest sha256 `ae6b35f2235de3a9a76435467bd2bd7405129b9199ab2175a1a49fb9e9b4fcff`. Every original v1 byte and its qualification remains unchanged. This adds exactly two qualified omitted fields and supplies the resulting three existing recovery procedure bodies. It introduces no new runtime procedure, counter, source primitive, callback, input, opcode, fee, or numeric listing.

The v1 projection omits `.work` but leaves two fields initialized from that omitted scalar. Those two fields have no retained consumer and must also be projected. The active omitted-field list is the v1 list plus:

1. `OrdinaryDispatch.RecoveryLocalWork.Built.coloring : Nat`, declared in RWInitial.lean9.
2. `OrdinaryDispatch.RecoveryLocalWork.InitialMeasured.coloring : Nat`, declared in RWInitial.lean37.

These are the two exact fields of module RWInitial, not a rule deleting fields named color or coloring elsewhere. Their logical source definitions remain visible in the frozen appendix and may be used in mathematical accounting. The runtime has no slot or dummy zero for either field. Since `.work` was already omitted, each of these projected wrappers now has only `value` left and uses v1's explicit single-value unboxing rule: Built represents its actual GTree directly; InitialMeasured represents its actual Option(Nat×GTree) directly.

## Exact producer and consumer chain

All ranges below are the original source lines in the already frozen pure view. RWInitial's context is `namespace OrdinaryDispatch.RecoveryLocalWork`.

|Source position|Original expression and its active role|
|---|---|
|Built9|Declares diagnostic Nat coloring. Its separate `value:GTree` remains.|
|meterBuild12|Leaf evaluates `a:=color x` once. `a.value` becomes the actual Group.color. `a.work` initializes Built.coloring and also contributes to the already omitted Built.work. Both scalar accounting uses are omitted; the color call and real returned color are retained.|
|meterBuild13–14|Evaluate left build on p++[false], then right build on p++[true]. Their real trees construct `.node p a.value b.value`. `a.coloring+b.coloring` only constructs the new Built.coloring and is omitted, including its field loads/addition.|
|InitialMeasured37|Declares the second diagnostic Nat coloring. Its separate `value:Option(Nat×GTree)` remains.|
|meterInitial40–44|Leaves/Nodup, second Leaves/length and real meterBuild execute at their original positions. `built.value` and `min budget (len.value-1)` construct the retained Some pair. `built.coloring` only initializes InitialMeasured.coloring and is omitted.|
|meterInitial45|On failed properness the retained answer remains None. The coloring zero constructor field is omitted rather than stored as a placeholder.|
|meterGenerate82–86|Its only retained initialization projection is `init.value`. `init.work` already feeds omitted accounting. There is no init.coloring read. The None receipt or the actual meterRun q built [] [] result stays unchanged.|

The complete finite coloring-field read set is meterBuild14 and meterInitial44. The two declarations and leaf initialization are the remaining coloring mentions in the frozen computational appendix. No guard, budget, callback argument, GTree/Group constructor, output constructor or return decision reads either diagnostic field. In particular Group.color is initialized from `a.value`, not from `a.work` or `a.coloring`.

## Resulting existing runtime procedure bodies

These are the active projected bodies of RWInitial.meterBuild, meterInitial and meterGenerate. They replace the corresponding projected interpretation of the existing bodies; they are not additional call targets. Calls and constructors are paid according to the unchanged v1 representation/operation specification. `color` is the same fixed real color adapter, whose projected result is its actual Nat value. It is never an answer/work oracle.

```text
meterBuild(color,p,Leaf(x)):
    c := color(x)                              // once; actual returned Nat color
    return GLeaf(Group(origin=p,labels=[x],color=c))
meterBuild(color,p,Node(l,r)):
    a := meterBuild(color,append(p,[false]),l)   // path construction then whole left
    b := meterBuild(color,append(p,[true]),r)    // then path and whole right
    return GNode(origin=p,left=a,right=b)

meterInitial(color,budget,t):
    leaves1 := meterLeaves(t)
    proper := meterNodup(leaves1)
    if not proper: return None
    leaves2 := meterLeaves(t)
    len := meterLength(leaves2)
    built := meterBuild(color,[],t)
    return Some(min(budget,sub(len,1)),built)

meterGenerate(t,color,budget):
    init := meterInitial(color,budget,t)
    case init of
      None:
        return Receipt(outputs=[],refusals=["duplicate original label"],
                       visited=0,childAttempts=0,pruned=0)
      Some(q,built):
        return meterRun(q,built,[],[])
```

In this code meterLeaves, meterNodup and meterLength mean their already specified projected value procedures, with actual traversals and paid returns. `sub` remains truncated natural subtraction. The explicit Receipt zeros in the malformed branch are the original retained Receipt values, not substitutes for deleted fields. The actual color adapter meterColor still executes its membership scans and supplies its real headD0/recursive result. All groups, paths, labels, color words, trees, min/length/budget tests and recursive generator calls remain real computations.

## Finite retained-field dependency catalogue

The catalogue distinguishes retained data from omitted accounting at the actual constructors. It adds no other field erasure. Original source locations and bodies are available through the v1 declaration/source indexes and the exact RWInitial entries bound by SOURCE-BINDING-v2.json.

|Retained family|Sources of retained fields and accounting boundary|
|---|---|
|GTree/Group, Local/Colors/Paint, typed tree/list/path data|The meterBuild leaf uses color(x).value; TableCost.meterTable leaf uses owner(x).value and node rows use their returned Paint values. Actual colors, origin paths, labels and chosen shapes remain; work sums only populate omitted accounting. `rows.map Charged.work` is in the already omitted table work expression, while `rows.map Charged.value` remains.|
|CoreProgram.Output and Receipt, RWLocal/RWRun receipts|Partition/sourceCuts come from actual generated data. outputs/refusals/visited/childAttempts/pruned come from literal constants and the corresponding retained receipt fields. For example meterAttempt15 increments r.value.childAttempts; it does not copy r.work. prefixRoot/combine operate on retained Receipt values. No broad colored/receipt field is projected.|
|Candidate, Child, Rule4.Branch, Entry/Mode, PaidRequest/Problem/Job|Costs and budgets come from literal paid counts, actual cut/partition/component lengths, retained additionalCost or scheduler cost results and the source budget arithmetic. No omitted work scalar supplies their retained fields. Branch.cost remains a fresh length(cuts) traversal at each written occurrence.|
|BestMeasured/ChoiceMeasured|Retained option/checks/tailSizes/comparisons use actual predicate results, current/tail values, real lengths and CutCost values. Their accounting sums stay in the omitted work field; a work scalar is not stored in a retained check or comparison.|
|CheckReceipt, ForestReceipt, ChildrenReceipt, CommonReceipt|Retained value/calls/agreementChecks are actual returned data, query parameters and concatenations. Numeric local/recursive work is confined to fields already omitted in v1. The child agreementChecks field remains r.value.|
|Scheduler receipts, LiteralReceiptSource and grouped evaluations|Retained answers, query/call cells and visits use real callback results, saved parameters and retained visit counts. callerWork/recursiveWork/localWork/callbackWork are already omitted; their words do not supply retained answers, queries or visits. The existing ordinaryCalls frontier diagnostic remains projected as declared in v1.|
|CurrentReceipt/PaidExecutionReceipt and single-value source wrappers|Only the retained value survives the previously declared projection; prefixWork/forestDebit/ordinaryCalls and pure source work remain omitted. These fields are not newly reclassified here.|
|Scan/Execution and ScanMeasured|Selected budget/forest, trials, actual recovered output and recoveries retain actual query/recovery results. work/administration remain omitted. No trial or recovery field is initialized from a work scalar.|
|Setup, LiteralGeometry, selected/raw choices and proof-bearing constructors|The released exact data selections retain trees/paths/labels/Booleans and values calculated by guards/builders. Full proof types remain logical obligations. Work-only bump/fee expressions do not feed the retained selections.|
|Work.Measured.copied/prunedCalls|These names occur only in that saved type declaration in the finite appendix, with no runtime constructor or consumer there. The amendment adds no field rule for them and does not change any receipt count.|
|Pure scalar escape expressions|checkFee/literalFee, concreteResiduals, callsForestDebit/childForestDebit/forestWork/nonrecursiveBill and their accounting-only contexts remain precisely the v1 omissions. They do not become runtime Nat data through this amendment.|

Thus the only additional work-to-retained-field path requiring a new omission at this boundary is the two-field Built.coloring→InitialMeasured.coloring chain above. This is a finite constructor/consumer argument for the supplied code, not a namespace-wide rule about names or a certificate of whole-algorithm cost.

## Preservation and control-bound transfer

Induct on the input tree for meterBuild. In a leaf, evaluate the same real color(x) call once and use the identical Nat result in the identical Group and GTree. The erased work/coloring arithmetic has no retained consumer. At a node the left induction hypothesis preserves its tree, events and order; then the right hypothesis does the same. The node uses only these trees and p, so its retained value is identical. The original coloring sum is unused outside the erased chain.

For meterInitial, the same first Leaves/Nodup result chooses the same branch. On true the same second Leaves/length and build sequence produce the identical capped budget and GTree; on false both return None. Its coloring output has no retained reader. For meterGenerate, matching that same option therefore yields the identical malformed Receipt or the same one meterRun invocation at the same q/built arguments. All later outputs/refusals/cuts and retained counters coincide. Actual callback occurrence multiplicity/order/results, ordinary selection, trial calls and the one recovery are unaffected.

These equalities are equalities of decoded retained typed data and software-call arguments/results, not identities of raw heap addresses. Removing wrapper fields changes later fresh addresses. The active representation and actual address/fee bounds must be established for the v2 allocations; no pointer equality or old-run bill equality is assumed.

No actual v1 cost theorem is inferred: the defect in its projected field dependency remains visible. The v1 text-derived S=367507, Fmax_slots=735030, Fmax_heap_words=2205090 and Kmax_return_tags=367508 remain conservative fixed control bounds for this deletion-only amendment. No new input/argument/callsite/control stage is added; the two field slots and their scalar arithmetic/projections disappear, and the two one-value wrappers unbox under the existing rule. Actual activation allocation uses only real fields, without padding. Local/global operation/width/space/source-counter proofs remain separate and must use this active v2 projection. This amendment supplies no numeric-program gate, acceptance result or complete runtime theorem.
