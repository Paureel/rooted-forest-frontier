import PaidDomains
namespace Universal233
open RMAF CoreGraph HardParent Rule5PaidSelector Rule5FinalClassification
set_option pp.explicit true in
#print Rule5PaidSelector.instDecidableLiteralProps
#print BadSelection
#check Case322Extraction.EndpointOrder
#eval decide (LiteralProps (.node (.leaf 0) (.leaf 0)) (.leaf 0) 0 1 ⟨[],0⟩ [] [] ⟨[],false,false,false,0,1,.leaf 0⟩ (.leaf 0) [] [])
end Universal233
