import BadPairSourceComplete
namespace OrdinaryDispatch.Hard2SourceWork

/-- A syntax-only explicit polynomial: addition, multiplication and fixed
natural powers only. The largest total degree is 14, through f (N*N+N+1).
This expression uses no source/work/handler oracle or budget-dependent power. -/
def badPairLocalPolynomialExpression (N Q : Nat) : Nat :=
 let a := fun n:Nat=>1024*(12*n+2)^5
 let g :=128*(N+1)^3+16*(1024*(N*(N+2)+N+2)^3+6)+12
 let cheap :=g*(Q+1)+N*(12*(N+1)+8)
 let plan :=4*cheap+(2*Q+24)*6+402000*(N+1)^6+128
 let ordinary :=(401000*(N+1)^6+8)*N+2+128*(N+1)+
  (64*(N+1)^2)*N+(2*N+12)*N+6+(32*(N+1)^2+12)*N+2+16
 let payload :=2*N*N+4*N+4
 let dispatch :=ordinary+((4*(N+2)*N+3)*N+1)+16*(N+1)^2+64*(N+1)^3+2*N+64
 let execution :=dispatch+a payload+payload+4*N+30
 let localTerm :=2*(plan+6*execution+56*(N+1)^3+128*(N+1)^2+22)+6
 let unchanged :=fun n:Nat=>(8*(n+1)^2+4)*(n+1)
 let cut :=fun n:Nat=>(8*(n+1)*n+4)+(128*(n+1)^3+unchanged n+16)*(n+1)+
  (8*(n+1)^2+12)*(n+1)+2*n+12
 let construction :=fun n:Nat=>unchanged n+cut n*n+6
 let f :=fun n:Nat=>164*(n+1)^3+construction n+(888*(2*n+3)^6+2*(2*n+5)+12)*(n+1)+18
 let prepare :=fun n:Nat=>f n+2*n+21
 let problem :=16*(N+1)^2+64*(N+1)^3+12
 let jobs :=(4*(N+2)*N+8)*(N+1)+2*N+4+3*(problem+4)+2*(prepare (N*N+N+1)+8)+18
 let run :=2*N+jobs+384+2*(2*N+16)+20
 let evaluate :=run+4*N+58
 let best :=a N+6*N+28
 let pair :=56*(N+1)^3+(2*cheap+10)+6*evaluate+6*best+24
 let grouped :=2*(pair+148+128*(N+1)^2+8)+6
 localTerm+grouped

theorem badPairLocalPolynomial_explicit (N Q : Nat) :
 badPairLocalPolynomial N Q=badPairLocalPolynomialExpression N Q := by rfl

theorem badPairSourcePolynomial_explicit (N Q : Nat) :
 badPairSourcePolynomial N Q=(badPairLocalPolynomialExpression N Q:Rat)+
  (400000000/417428121:Rat)*((2^50*(N+Q+2)^8:Nat):Rat) := by rfl
end OrdinaryDispatch.Hard2SourceWork
