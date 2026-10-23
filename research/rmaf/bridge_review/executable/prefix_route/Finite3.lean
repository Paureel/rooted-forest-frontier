import RMAF

namespace PrefixRouteFinite
open RMAF
def sameMembers (xs ys : List Vertex) : Bool :=
  xs.all (fun x => ys.contains x) && ys.all (fun y => xs.contains y)

theorem control_cross : sameMembers (minimalVertices [0, 2] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))) [[], [false], [false, false], [true], [true, false]] = true := by decide
theorem control_singleton : sameMembers (minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))) [[false, true]] = true := by decide
theorem control_left_pair : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))) [[false], [false, false], [false, true]] = true := by decide
theorem control_empty_selection : sameMembers (minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))) [] = true := by decide
theorem control_absent_label : sameMembers (minimalVertices [9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))) [] = true := by decide
theorem control_duplicate_label : sameMembers (minimalVertices [7] (.node (.node (.leaf 7) (.leaf 1)) (.node (.leaf 2) (.leaf 7)))) [[], [false], [false, false], [true], [true, true]] = true := by decide
theorem control_mixed_absent : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 7) (.leaf 1)) (.node (.leaf 2) (.leaf 7)))) [[false, true]] = true := by decide
theorem control_long_left_pair : sameMembers (minimalVertices [0, 1] (.node (.leaf 8) (.node (.leaf 8) (.node (.leaf 8) (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))))))) [[true, true, true, false], [true, true, true, false, false], [true, true, true, false, true]] = true := by decide
theorem control_long_cross : sameMembers (minimalVertices [0, 2] (.node (.leaf 8) (.node (.leaf 8) (.node (.leaf 8) (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))))))) [[true, true, true], [true, true, true, false], [true, true, true, false, false], [true, true, true, true], [true, true, true, true, false]] = true := by decide
theorem reject_missing_path : sameMembers (minimalVertices [0, 2] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))) [[], [false, false], [true], [true, false]] = false := by decide
theorem reject_wrong_absent_label : sameMembers (minimalVertices [9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3)))) [[]] = false := by decide
theorem reject_one_duplicate_only : sameMembers (minimalVertices [7] (.node (.node (.leaf 7) (.leaf 1)) (.node (.leaf 2) (.leaf 7)))) [[false, false]] = false := by decide
theorem reject_unsuppressed_initial_path : sameMembers (minimalVertices [0, 2] (.node (.leaf 8) (.node (.leaf 8) (.node (.leaf 8) (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))))))) [[], [true], [true, true], [true, true, true], [true, true, true, false], [true, true, true, false, false], [true, true, true, true], [true, true, true, true, false]] = false := by decide

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem sweep_0000 : sameMembers (minimalVertices [] (.leaf 0)) [] = true := by decide
theorem sweep_0001 : sameMembers (minimalVertices [9] (.leaf 0)) [] = true := by decide
theorem sweep_0002 : sameMembers (minimalVertices [1] (.leaf 0)) [] = true := by decide
theorem sweep_0003 : sameMembers (minimalVertices [1, 9] (.leaf 0)) [] = true := by decide
theorem sweep_0004 : sameMembers (minimalVertices [0] (.leaf 0)) [[]] = true := by decide
theorem sweep_0005 : sameMembers (minimalVertices [0, 9] (.leaf 0)) [[]] = true := by decide
theorem sweep_0006 : sameMembers (minimalVertices [0, 1] (.leaf 0)) [[]] = true := by decide
theorem sweep_0007 : sameMembers (minimalVertices [0, 1, 9] (.leaf 0)) [[]] = true := by decide
theorem sweep_0008 : sameMembers (minimalVertices [] (.leaf 1)) [] = true := by decide
theorem sweep_0009 : sameMembers (minimalVertices [9] (.leaf 1)) [] = true := by decide
theorem sweep_0010 : sameMembers (minimalVertices [1] (.leaf 1)) [[]] = true := by decide
theorem sweep_0011 : sameMembers (minimalVertices [1, 9] (.leaf 1)) [[]] = true := by decide
theorem sweep_0012 : sameMembers (minimalVertices [0] (.leaf 1)) [] = true := by decide
theorem sweep_0013 : sameMembers (minimalVertices [0, 9] (.leaf 1)) [] = true := by decide
theorem sweep_0014 : sameMembers (minimalVertices [0, 1] (.leaf 1)) [[]] = true := by decide
theorem sweep_0015 : sameMembers (minimalVertices [0, 1, 9] (.leaf 1)) [[]] = true := by decide
theorem sweep_0016 : sameMembers (minimalVertices [] (.node (.leaf 0) (.leaf 0))) [] = true := by decide
theorem sweep_0017 : sameMembers (minimalVertices [9] (.node (.leaf 0) (.leaf 0))) [] = true := by decide
theorem sweep_0018 : sameMembers (minimalVertices [1] (.node (.leaf 0) (.leaf 0))) [] = true := by decide
theorem sweep_0019 : sameMembers (minimalVertices [1, 9] (.node (.leaf 0) (.leaf 0))) [] = true := by decide
theorem sweep_0020 : sameMembers (minimalVertices [0] (.node (.leaf 0) (.leaf 0))) [[], [false], [true]] = true := by decide
theorem sweep_0021 : sameMembers (minimalVertices [0, 9] (.node (.leaf 0) (.leaf 0))) [[], [false], [true]] = true := by decide
theorem sweep_0022 : sameMembers (minimalVertices [0, 1] (.node (.leaf 0) (.leaf 0))) [[], [false], [true]] = true := by decide
theorem sweep_0023 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 0) (.leaf 0))) [[], [false], [true]] = true := by decide
theorem sweep_0024 : sameMembers (minimalVertices [] (.node (.leaf 0) (.leaf 1))) [] = true := by decide
theorem sweep_0025 : sameMembers (minimalVertices [9] (.node (.leaf 0) (.leaf 1))) [] = true := by decide
theorem sweep_0026 : sameMembers (minimalVertices [1] (.node (.leaf 0) (.leaf 1))) [[true]] = true := by decide
theorem sweep_0027 : sameMembers (minimalVertices [1, 9] (.node (.leaf 0) (.leaf 1))) [[true]] = true := by decide
theorem sweep_0028 : sameMembers (minimalVertices [0] (.node (.leaf 0) (.leaf 1))) [[false]] = true := by decide
theorem sweep_0029 : sameMembers (minimalVertices [0, 9] (.node (.leaf 0) (.leaf 1))) [[false]] = true := by decide
theorem sweep_0030 : sameMembers (minimalVertices [0, 1] (.node (.leaf 0) (.leaf 1))) [[], [false], [true]] = true := by decide
theorem sweep_0031 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 0) (.leaf 1))) [[], [false], [true]] = true := by decide
theorem sweep_0032 : sameMembers (minimalVertices [] (.node (.leaf 1) (.leaf 0))) [] = true := by decide
theorem sweep_0033 : sameMembers (minimalVertices [9] (.node (.leaf 1) (.leaf 0))) [] = true := by decide
theorem sweep_0034 : sameMembers (minimalVertices [1] (.node (.leaf 1) (.leaf 0))) [[false]] = true := by decide
theorem sweep_0035 : sameMembers (minimalVertices [1, 9] (.node (.leaf 1) (.leaf 0))) [[false]] = true := by decide
theorem sweep_0036 : sameMembers (minimalVertices [0] (.node (.leaf 1) (.leaf 0))) [[true]] = true := by decide
theorem sweep_0037 : sameMembers (minimalVertices [0, 9] (.node (.leaf 1) (.leaf 0))) [[true]] = true := by decide
theorem sweep_0038 : sameMembers (minimalVertices [0, 1] (.node (.leaf 1) (.leaf 0))) [[], [false], [true]] = true := by decide
theorem sweep_0039 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 1) (.leaf 0))) [[], [false], [true]] = true := by decide
theorem sweep_0040 : sameMembers (minimalVertices [] (.node (.leaf 1) (.leaf 1))) [] = true := by decide
theorem sweep_0041 : sameMembers (minimalVertices [9] (.node (.leaf 1) (.leaf 1))) [] = true := by decide
theorem sweep_0042 : sameMembers (minimalVertices [1] (.node (.leaf 1) (.leaf 1))) [[], [false], [true]] = true := by decide
theorem sweep_0043 : sameMembers (minimalVertices [1, 9] (.node (.leaf 1) (.leaf 1))) [[], [false], [true]] = true := by decide
theorem sweep_0044 : sameMembers (minimalVertices [0] (.node (.leaf 1) (.leaf 1))) [] = true := by decide
theorem sweep_0045 : sameMembers (minimalVertices [0, 9] (.node (.leaf 1) (.leaf 1))) [] = true := by decide
theorem sweep_0046 : sameMembers (minimalVertices [0, 1] (.node (.leaf 1) (.leaf 1))) [[], [false], [true]] = true := by decide
theorem sweep_0047 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 1) (.leaf 1))) [[], [false], [true]] = true := by decide
theorem sweep_0048 : sameMembers (minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) [] = true := by decide
theorem sweep_0049 : sameMembers (minimalVertices [9] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) [] = true := by decide
theorem sweep_0050 : sameMembers (minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) [] = true := by decide
theorem sweep_0051 : sameMembers (minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) [] = true := by decide
theorem sweep_0052 : sameMembers (minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) [[], [false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0053 : sameMembers (minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) [[], [false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0054 : sameMembers (minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) [[], [false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0055 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) [[], [false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0056 : sameMembers (minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) [] = true := by decide
theorem sweep_0057 : sameMembers (minimalVertices [9] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) [] = true := by decide
theorem sweep_0058 : sameMembers (minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) [[true, true]] = true := by decide
theorem sweep_0059 : sameMembers (minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) [[true, true]] = true := by decide
theorem sweep_0060 : sameMembers (minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) [[], [false], [true], [true, false]] = true := by decide
theorem sweep_0061 : sameMembers (minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) [[], [false], [true], [true, false]] = true := by decide
theorem sweep_0062 : sameMembers (minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) [[], [false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0063 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) [[], [false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0064 : sameMembers (minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) [] = true := by decide
theorem sweep_0065 : sameMembers (minimalVertices [9] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) [] = true := by decide
theorem sweep_0066 : sameMembers (minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) [[true, false]] = true := by decide
theorem sweep_0067 : sameMembers (minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) [[true, false]] = true := by decide
theorem sweep_0068 : sameMembers (minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) [[], [false], [true], [true, true]] = true := by decide
theorem sweep_0069 : sameMembers (minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) [[], [false], [true], [true, true]] = true := by decide
theorem sweep_0070 : sameMembers (minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) [[], [false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0071 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) [[], [false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0072 : sameMembers (minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) [] = true := by decide
theorem sweep_0073 : sameMembers (minimalVertices [9] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) [] = true := by decide
theorem sweep_0074 : sameMembers (minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) [[true], [true, false], [true, true]] = true := by decide
theorem sweep_0075 : sameMembers (minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) [[true], [true, false], [true, true]] = true := by decide
theorem sweep_0076 : sameMembers (minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) [[false]] = true := by decide
theorem sweep_0077 : sameMembers (minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) [[false]] = true := by decide
theorem sweep_0078 : sameMembers (minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) [[], [false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0079 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) [[], [false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0080 : sameMembers (minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) [] = true := by decide
theorem sweep_0081 : sameMembers (minimalVertices [9] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) [] = true := by decide
theorem sweep_0082 : sameMembers (minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) [[false]] = true := by decide
theorem sweep_0083 : sameMembers (minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) [[false]] = true := by decide
theorem sweep_0084 : sameMembers (minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) [[true], [true, false], [true, true]] = true := by decide
theorem sweep_0085 : sameMembers (minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) [[true], [true, false], [true, true]] = true := by decide
theorem sweep_0086 : sameMembers (minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) [[], [false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0087 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) [[], [false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0088 : sameMembers (minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) [] = true := by decide
theorem sweep_0089 : sameMembers (minimalVertices [9] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) [] = true := by decide
theorem sweep_0090 : sameMembers (minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) [[], [false], [true], [true, true]] = true := by decide
theorem sweep_0091 : sameMembers (minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) [[], [false], [true], [true, true]] = true := by decide
theorem sweep_0092 : sameMembers (minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) [[true, false]] = true := by decide
theorem sweep_0093 : sameMembers (minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) [[true, false]] = true := by decide
theorem sweep_0094 : sameMembers (minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) [[], [false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0095 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) [[], [false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0096 : sameMembers (minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) [] = true := by decide
theorem sweep_0097 : sameMembers (minimalVertices [9] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) [] = true := by decide
theorem sweep_0098 : sameMembers (minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) [[], [false], [true], [true, false]] = true := by decide
theorem sweep_0099 : sameMembers (minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) [[], [false], [true], [true, false]] = true := by decide
theorem sweep_0100 : sameMembers (minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) [[true, true]] = true := by decide
theorem sweep_0101 : sameMembers (minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) [[true, true]] = true := by decide
theorem sweep_0102 : sameMembers (minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) [[], [false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0103 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) [[], [false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0104 : sameMembers (minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) [] = true := by decide
theorem sweep_0105 : sameMembers (minimalVertices [9] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) [] = true := by decide
theorem sweep_0106 : sameMembers (minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) [[], [false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0107 : sameMembers (minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) [[], [false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0108 : sameMembers (minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) [] = true := by decide
theorem sweep_0109 : sameMembers (minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) [] = true := by decide
theorem sweep_0110 : sameMembers (minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) [[], [false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0111 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) [[], [false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0112 : sameMembers (minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) [] = true := by decide
theorem sweep_0113 : sameMembers (minimalVertices [9] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) [] = true := by decide
theorem sweep_0114 : sameMembers (minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) [] = true := by decide
theorem sweep_0115 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) [] = true := by decide
theorem sweep_0116 : sameMembers (minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) [[], [false], [false, false], [false, true], [true]] = true := by decide
theorem sweep_0117 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) [[], [false], [false, false], [false, true], [true]] = true := by decide
theorem sweep_0118 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) [[], [false], [false, false], [false, true], [true]] = true := by decide
theorem sweep_0119 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) [[], [false], [false, false], [false, true], [true]] = true := by decide
theorem sweep_0120 : sameMembers (minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) [] = true := by decide
theorem sweep_0121 : sameMembers (minimalVertices [9] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) [] = true := by decide
theorem sweep_0122 : sameMembers (minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) [[true]] = true := by decide
theorem sweep_0123 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) [[true]] = true := by decide
theorem sweep_0124 : sameMembers (minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) [[false], [false, false], [false, true]] = true := by decide
theorem sweep_0125 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) [[false], [false, false], [false, true]] = true := by decide
theorem sweep_0126 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) [[], [false], [false, false], [false, true], [true]] = true := by decide
theorem sweep_0127 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) [[], [false], [false, false], [false, true], [true]] = true := by decide
theorem sweep_0128 : sameMembers (minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) [] = true := by decide
theorem sweep_0129 : sameMembers (minimalVertices [9] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) [] = true := by decide
theorem sweep_0130 : sameMembers (minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) [[false, true]] = true := by decide
theorem sweep_0131 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) [[false, true]] = true := by decide
theorem sweep_0132 : sameMembers (minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) [[], [false], [false, false], [true]] = true := by decide
theorem sweep_0133 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) [[], [false], [false, false], [true]] = true := by decide
theorem sweep_0134 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) [[], [false], [false, false], [false, true], [true]] = true := by decide
theorem sweep_0135 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) [[], [false], [false, false], [false, true], [true]] = true := by decide
theorem sweep_0136 : sameMembers (minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) [] = true := by decide
theorem sweep_0137 : sameMembers (minimalVertices [9] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) [] = true := by decide
theorem sweep_0138 : sameMembers (minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) [[], [false], [false, true], [true]] = true := by decide
theorem sweep_0139 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) [[], [false], [false, true], [true]] = true := by decide
theorem sweep_0140 : sameMembers (minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) [[false, false]] = true := by decide
theorem sweep_0141 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) [[false, false]] = true := by decide
theorem sweep_0142 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) [[], [false], [false, false], [false, true], [true]] = true := by decide
theorem sweep_0143 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) [[], [false], [false, false], [false, true], [true]] = true := by decide
theorem sweep_0144 : sameMembers (minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) [] = true := by decide
theorem sweep_0145 : sameMembers (minimalVertices [9] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) [] = true := by decide
theorem sweep_0146 : sameMembers (minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) [[false, false]] = true := by decide
theorem sweep_0147 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) [[false, false]] = true := by decide
theorem sweep_0148 : sameMembers (minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) [[], [false], [false, true], [true]] = true := by decide
theorem sweep_0149 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) [[], [false], [false, true], [true]] = true := by decide
theorem sweep_0150 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) [[], [false], [false, false], [false, true], [true]] = true := by decide
theorem sweep_0151 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) [[], [false], [false, false], [false, true], [true]] = true := by decide
theorem sweep_0152 : sameMembers (minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) [] = true := by decide
theorem sweep_0153 : sameMembers (minimalVertices [9] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) [] = true := by decide
theorem sweep_0154 : sameMembers (minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) [[], [false], [false, false], [true]] = true := by decide
theorem sweep_0155 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) [[], [false], [false, false], [true]] = true := by decide
theorem sweep_0156 : sameMembers (minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) [[false, true]] = true := by decide
theorem sweep_0157 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) [[false, true]] = true := by decide
theorem sweep_0158 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) [[], [false], [false, false], [false, true], [true]] = true := by decide
theorem sweep_0159 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) [[], [false], [false, false], [false, true], [true]] = true := by decide
theorem sweep_0160 : sameMembers (minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) [] = true := by decide
theorem sweep_0161 : sameMembers (minimalVertices [9] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) [] = true := by decide
theorem sweep_0162 : sameMembers (minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) [[false], [false, false], [false, true]] = true := by decide
theorem sweep_0163 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) [[false], [false, false], [false, true]] = true := by decide
theorem sweep_0164 : sameMembers (minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) [[true]] = true := by decide
theorem sweep_0165 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) [[true]] = true := by decide
theorem sweep_0166 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) [[], [false], [false, false], [false, true], [true]] = true := by decide
theorem sweep_0167 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) [[], [false], [false, false], [false, true], [true]] = true := by decide
theorem sweep_0168 : sameMembers (minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) [] = true := by decide
theorem sweep_0169 : sameMembers (minimalVertices [9] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) [] = true := by decide
theorem sweep_0170 : sameMembers (minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) [[], [false], [false, false], [false, true], [true]] = true := by decide
theorem sweep_0171 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) [[], [false], [false, false], [false, true], [true]] = true := by decide
theorem sweep_0172 : sameMembers (minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) [] = true := by decide
theorem sweep_0173 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) [] = true := by decide
theorem sweep_0174 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) [[], [false], [false, false], [false, true], [true]] = true := by decide
theorem sweep_0175 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) [[], [false], [false, false], [false, true], [true]] = true := by decide

#print axioms control_cross
#print axioms control_singleton
#print axioms control_left_pair
#print axioms control_empty_selection
#print axioms control_absent_label
#print axioms control_duplicate_label
#print axioms control_mixed_absent
#print axioms control_long_left_pair
#print axioms control_long_cross
#print axioms reject_missing_path
#print axioms reject_wrong_absent_label
#print axioms reject_one_duplicate_only
#print axioms reject_unsuppressed_initial_path
#print axioms sweep_0000
#print axioms sweep_0175
end PrefixRouteFinite
