import StoredSourceControls
import StoredOrientations
namespace OrdinaryDispatch.StoredNumeric.Controls
open GenericForest.BinaryProvider

theorem reverse_actual_constructor :
 OrientedStep tinyT tinyS (contractPairBits [true] [false,true] tinyS tinyT).value.1
  (contractPairBits [true] [false,true] tinyS tinyT).value.2 := by
 right
 apply StoredStep.common <;> simp [tinyS,tinyT,leavesBits]
end OrdinaryDispatch.StoredNumeric.Controls
