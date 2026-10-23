# Literal source controls, frozen before new proof construction

These exact expected values are written manually from the already retrieved literal source definitions. They are production-side tests; separate nonauthor certification remains required.

* On cherry node(leaf0,leaf1): leaf-address work for label0 is 8, for absent label9 is 12; absent result is none.
* For two identical arbitrary branches with one cut [false], q=0: answers=[] and answer-source work=13 (two rejected affordability tests, 6 each, plus base1). Null list work=1.
* Literal cuts [false],[true] retain partition [[0],[1],[]]; source restriction materialization removes only the empty block and leaves leaf0,leaf1. This tests empty-region materialization.
* On T=((0,1),(2,3)), S=((0,2),(1,3)), raw(a=0,b=1,c=2,cHead=[false,true],xHead=[true,true]) is a valid Rule4 Choice with literal branch costs [2,1,2]. Its q=0 output is none and source work is positive.
* Hostile mutations: leaf-address miss claimed as8 (omits visited second subtree), rejected duplicate one-cut branch work claimed as7 (deduplicates), literal partition claimed [[0],[1]] (omits empty region). Each must fail with a mathematical compiler rejection.
* Clean/corrupt manifest twin: hash compare must accept clean bytes, reject appended newline copy; original frozen manifest is never edited.
