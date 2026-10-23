# Prospective composed-arithmetic check

Frozen before writing/running the one-shot script and before any Phase C arithmetic output exists. The candidate mathematical arguments have already been read; this is explicitly a post-argument exact algebra check, not a retroactive cold control or a candidate execution. Phase A and the initial/follow-on seals remain unchanged. The TARGET-v3 Phase C requirement to machine-check new composed arithmetic applies. Earlier wording that no Phase C computation was necessary will be corrected additively in the unsealed draft.

Method: a small standard-library integer/Fraction script written here, importing no project computation, theorem, verifier, original source or prior checker. Positive/manual fixtures below calibrate its formulas and comparisons, followed by four deliberately corrupted expressions. No general verification framework or symbolic/numeric certification is introduced. All values are exact naturals/rationals. Run each mode once with the existing pinned run_capped.py, omit --seconds to retain default30s, existing shared lock, no cap raise. Positive expected exit0; corrupt expected exit23 only after all four exact diagnostics. Unexpected failures remain evidence and require prospective correction, never rescore.

The operations are a few fixed powers on integers of at most a few thousand bits. Existing small arithmetic runs were around0.03s; this new expression set is not timed in advance. Default30s is the hard existing child cap, no long run is planned. No candidate helper/body executes. Semantic outputs, logs/receipts, script/preregistration pins and runtime/platform qualification will be retained.

## Manual exact positive expectations

- C1 corrected payload: the22 displayed coefficients sum to108400. At a=2 the merge expression4608a^3+192a^2+1=37633, its5120a^3 bound40960, margin3327. The corrected environment296a^2+3416a+160=8176 and2048a^2=8192, margin16. Eighteen environments at the bound plus256 give147712 versus20480a^3=163840, margin16128.
- C2 finite constants: f735030,c367508 give F=9f=6615270, gamma=9f^2+63f+3c+62=4862469317576 and s=3f+c+128=2572726.
- C3 materialization: at m=0,x=(m+1)^3=1, the active maximum is2^30=1073741824; times16 equals J=2^34=17179869184. The superseded maximum without2^30 would be2^22=4194304.
- C4 coefficient exponents:48+10*19=238; adding6,7,8 gives244,245,246. K's252 minus246 leaves6 powers of2;32 minus30 leaves2 powers ofR. Expected [238,244,245,246,6,2].
- C5 degrees: Z has4+4*32=132; T has132+4*16=196; J has max(2,32+16)=48; B max(2,196,48,1)=196; A max(6,32+2*196)=424; final multiplier424+16=440. Expected [132,196,48,196,424,440].
- C6 small full gluing fixture, separate from candidate constants: Q2,P10,C50,K3,U153,H05,F2,s1,R1,D3,I7,gamma2. r=233/100, so C<=Pr^2=54289/1000 and C+1<=11r^2=597179/10000. J=71,Z4096,T59969536,B59969634,H311. Scalar cap2^3+16*(153+1)^4=8999178504, width34; pointer width9. The source/allocation/scalar/pointer derived inequalities must be true. With per=16gamma(B+1)^2, A=I+K*per, the RHS A(C+1) minus [I+per*U] is exactly350. This tests the same dependency direction: count before allocation before widths before fees, with source inequality used only after the count.
- C7 plus-one absorption: at d2,P'=1, local64*(d+1)=192, valid128*d=256, slack64. This fixture is distinct from the earlier optimizer recurrence control.

## Deliberate corruptions and exact diagnostic contract

- N1 drops the2^30 materialization term: diagnostic MATERIALIZATION_MAX_TERM, expected1073741824, observed4194304.
- N2 replaces (P+1)^4 by (P+1)^3 in T's degree: diagnostic SCALAR_POWER_MULTIPLICITY, expected196, observed180.
- N3 drops +1 from count consumption at C0,K3,U3: diagnostic COUNT_PLUS_ONE, expected3, observed0.
- N4 omits the factor2 in d+1 absorption at d2,P'=1: diagnostic LOCAL_PLUS_ONE_ABSORPTION, expected192, observed128.

The clean cases validate exact arithmetic expectations; planted cases validate rejection and exact diagnostics. They do not establish universal inequalities by finite sampling. Universal derivations remain the written induction/algebra in the final report. Shared Python/runtime is explicitly qualified; no independent engine/kernel claim is permitted.
