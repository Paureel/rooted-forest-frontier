import ClassifierFeeBinding
import ClassifierFeePolynomial
namespace Universal233.ClassifierCheckFee
open RMAF CoreWork Rule5PendantLocalWork Rule5RemainingLocalWork
open GenericForest.CheckCorrespondence PaidLiteralDecisionWork
set_option maxRecDepth 24000
set_option maxHeartbeats 1000000

instance checkDomainDecidable (N L : Nat) (r : CheckRequest) : Decidable (CheckDomain N L r) := by
 cases r <;> unfold CheckDomain <;> infer_instance

def target2 : Tree:=.node (.leaf 0) (.leaf 1)
def repeated2 : Tree:=.node (.leaf 0) (.leaf 0)
def successEmbedding : CheckRequest:=.embedding target2 [[0],[1]]
def falseEmbedding : CheckRequest:=.embedding target2 [[0,1],[0]]
def successRestriction : CheckRequest:=.restriction target2 target2 [0,1]
def falseRestriction : CheckRequest:=.restriction target2 (.leaf 0) [0,1]

theorem known_embedding_domain : CheckDomain 2 1 successEmbedding := by decide
theorem hostile_embedding_domain : CheckDomain 2 1 falseEmbedding := by decide
theorem known_restriction_domain : CheckDomain 2 1 successRestriction := by decide
theorem hostile_restriction_domain : CheckDomain 2 1 falseRestriction := by decide

def requestControl (r : CheckRequest) (expected : Bool) : Bool:=
 decide ((requestMeter r).value=expected) &&
 decide ((requestMeter r).value=checkValue r) &&
 decide ((requestMeter r).calls=[r]) &&
 decide ((checkMeter checkFee r).work=(requestMeter r).work) &&
 decide (checkFee r≤checkCap 2)

def controls : List (String×Bool):=
 [("embedding_one_block",requestControl (.embedding target2 [[0,1]]) true),
  ("embedding_disjoint_singletons",requestControl successEmbedding true),
  ("embedding_overlap_rejected",requestControl falseEmbedding false),
  ("embedding_empty",requestControl (.embedding target2 []) true),
  ("embedding_empty_blocks",requestControl (.embedding target2 [[],[]]) true),
  ("restriction_identical",requestControl successRestriction true),
  ("restriction_shape_mismatch",requestControl falseRestriction false),
  ("restriction_empty_refused",requestControl (.restriction target2 target2 []) false),
  ("restriction_missing_taxon_refused",requestControl (.restriction target2 (.leaf 9) [0]) false),
  ("restriction_singleton_agrees",requestControl (.restriction target2 (.leaf 0) [0]) true),
  ("out_of_domain_blocks_rejected",decide (¬CheckDomain 2 1 (.embedding target2 (List.replicate 6 [0])))),
  ("out_of_domain_labels_rejected",decide (¬CheckDomain 2 1 (.restriction target2 (.leaf 9) [0]))),
  ("block_payload_nonempty",decide (([0,1]:List Nat).length≤([[0,1],[0]]:List (List Nat)).flatten.length)),
  ("cap_polynomial_N2",decide (checkCap 2=120*(2*2*2+2*2+2)^5+128*3^2+2)),
  ("final_value_identical",decide ((finalSourceMeter target2 target2 0 1).value=(finalMeter checkFee target2 target2 0 1).value)),
  ("final_value_refusal",decide ((finalSourceMeter repeated2 target2 0 1).value.isNone=true)),
  ("paid_builder_refusal",decide ((paidBuilderSourceMeter target2 target2 0 1).value.isNone=true)),
  ("corrupt_zero_fee_detected",decide (checkFee successEmbedding≠0))]
#eval controls
#eval ("CLASSIFIER_FEE_CONTROLS",controls.length,controls.all Prod.snd)
#eval ("REQUEST_BILLS",checkFee successEmbedding,checkFee falseEmbedding,checkFee successRestriction,checkFee falseRestriction,"CAP_N2",checkCap 2)
#print axioms request_value
#print axioms check_fee_bound
#print axioms final_source_work
#print axioms paid_builder_work
end Universal233.ClassifierCheckFee
