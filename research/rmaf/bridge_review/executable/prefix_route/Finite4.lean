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
theorem sweep_0176 : sameMembers (minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))))) [] = true := by decide
theorem sweep_0177 : sameMembers (minimalVertices [9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))))) [] = true := by decide
theorem sweep_0178 : sameMembers (minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))))) [] = true := by decide
theorem sweep_0179 : sameMembers (minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))))) [] = true := by decide
theorem sweep_0180 : sameMembers (minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0181 : sameMembers (minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0182 : sameMembers (minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0183 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0184 : sameMembers (minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))))) [] = true := by decide
theorem sweep_0185 : sameMembers (minimalVertices [9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))))) [] = true := by decide
theorem sweep_0186 : sameMembers (minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))))) [[true, true, true]] = true := by decide
theorem sweep_0187 : sameMembers (minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))))) [[true, true, true]] = true := by decide
theorem sweep_0188 : sameMembers (minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))))) [[], [false], [true], [true, false], [true, true], [true, true, false]] = true := by decide
theorem sweep_0189 : sameMembers (minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))))) [[], [false], [true], [true, false], [true, true], [true, true, false]] = true := by decide
theorem sweep_0190 : sameMembers (minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0191 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0192 : sameMembers (minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))))) [] = true := by decide
theorem sweep_0193 : sameMembers (minimalVertices [9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))))) [] = true := by decide
theorem sweep_0194 : sameMembers (minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))))) [[true, true, false]] = true := by decide
theorem sweep_0195 : sameMembers (minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))))) [[true, true, false]] = true := by decide
theorem sweep_0196 : sameMembers (minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))))) [[], [false], [true], [true, false], [true, true], [true, true, true]] = true := by decide
theorem sweep_0197 : sameMembers (minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))))) [[], [false], [true], [true, false], [true, true], [true, true, true]] = true := by decide
theorem sweep_0198 : sameMembers (minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0199 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0200 : sameMembers (minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))))) [] = true := by decide
theorem sweep_0201 : sameMembers (minimalVertices [9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))))) [] = true := by decide
theorem sweep_0202 : sameMembers (minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))))) [[true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0203 : sameMembers (minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))))) [[true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0204 : sameMembers (minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))))) [[], [false], [true], [true, false]] = true := by decide
theorem sweep_0205 : sameMembers (minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))))) [[], [false], [true], [true, false]] = true := by decide
theorem sweep_0206 : sameMembers (minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0207 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0208 : sameMembers (minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))))) [] = true := by decide
theorem sweep_0209 : sameMembers (minimalVertices [9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))))) [] = true := by decide
theorem sweep_0210 : sameMembers (minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))))) [[true, false]] = true := by decide
theorem sweep_0211 : sameMembers (minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))))) [[true, false]] = true := by decide
theorem sweep_0212 : sameMembers (minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))))) [[], [false], [true], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0213 : sameMembers (minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))))) [[], [false], [true], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0214 : sameMembers (minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0215 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0216 : sameMembers (minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))))) [] = true := by decide
theorem sweep_0217 : sameMembers (minimalVertices [9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))))) [] = true := by decide
theorem sweep_0218 : sameMembers (minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))))) [[true], [true, false], [true, true], [true, true, true]] = true := by decide
theorem sweep_0219 : sameMembers (minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))))) [[true], [true, false], [true, true], [true, true, true]] = true := by decide
theorem sweep_0220 : sameMembers (minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))))) [[], [false], [true], [true, true], [true, true, false]] = true := by decide
theorem sweep_0221 : sameMembers (minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))))) [[], [false], [true], [true, true], [true, true, false]] = true := by decide
theorem sweep_0222 : sameMembers (minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0223 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0224 : sameMembers (minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))))) [] = true := by decide
theorem sweep_0225 : sameMembers (minimalVertices [9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))))) [] = true := by decide
theorem sweep_0226 : sameMembers (minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))))) [[true], [true, false], [true, true], [true, true, false]] = true := by decide
theorem sweep_0227 : sameMembers (minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))))) [[true], [true, false], [true, true], [true, true, false]] = true := by decide
theorem sweep_0228 : sameMembers (minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))))) [[], [false], [true], [true, true], [true, true, true]] = true := by decide
theorem sweep_0229 : sameMembers (minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))))) [[], [false], [true], [true, true], [true, true, true]] = true := by decide
theorem sweep_0230 : sameMembers (minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0231 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0232 : sameMembers (minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))))) [] = true := by decide
theorem sweep_0233 : sameMembers (minimalVertices [9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))))) [] = true := by decide
theorem sweep_0234 : sameMembers (minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))))) [[true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0235 : sameMembers (minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))))) [[true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0236 : sameMembers (minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))))) [[false]] = true := by decide
theorem sweep_0237 : sameMembers (minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))))) [[false]] = true := by decide
theorem sweep_0238 : sameMembers (minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0239 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0240 : sameMembers (minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)))) [] = true := by decide
theorem sweep_0241 : sameMembers (minimalVertices [9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)))) [] = true := by decide
theorem sweep_0242 : sameMembers (minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)))) [] = true := by decide
theorem sweep_0243 : sameMembers (minimalVertices [1, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)))) [] = true := by decide
theorem sweep_0244 : sameMembers (minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0245 : sameMembers (minimalVertices [0, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0246 : sameMembers (minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0247 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0248 : sameMembers (minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)))) [] = true := by decide
theorem sweep_0249 : sameMembers (minimalVertices [9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)))) [] = true := by decide
theorem sweep_0250 : sameMembers (minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)))) [[true, true]] = true := by decide
theorem sweep_0251 : sameMembers (minimalVertices [1, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)))) [[true, true]] = true := by decide
theorem sweep_0252 : sameMembers (minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true]] = true := by decide
theorem sweep_0253 : sameMembers (minimalVertices [0, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true]] = true := by decide
theorem sweep_0254 : sameMembers (minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0255 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0256 : sameMembers (minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)))) [] = true := by decide
theorem sweep_0257 : sameMembers (minimalVertices [9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)))) [] = true := by decide
theorem sweep_0258 : sameMembers (minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)))) [[true, false, true]] = true := by decide
theorem sweep_0259 : sameMembers (minimalVertices [1, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)))) [[true, false, true]] = true := by decide
theorem sweep_0260 : sameMembers (minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false], [true, true]] = true := by decide
theorem sweep_0261 : sameMembers (minimalVertices [0, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false], [true, true]] = true := by decide
theorem sweep_0262 : sameMembers (minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0263 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0264 : sameMembers (minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)))) [] = true := by decide
theorem sweep_0265 : sameMembers (minimalVertices [9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)))) [] = true := by decide
theorem sweep_0266 : sameMembers (minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)))) [[true], [true, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0267 : sameMembers (minimalVertices [1, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)))) [[true], [true, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0268 : sameMembers (minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false]] = true := by decide
theorem sweep_0269 : sameMembers (minimalVertices [0, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false]] = true := by decide
theorem sweep_0270 : sameMembers (minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0271 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0272 : sameMembers (minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)))) [] = true := by decide
theorem sweep_0273 : sameMembers (minimalVertices [9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)))) [] = true := by decide
theorem sweep_0274 : sameMembers (minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)))) [[true, false, false]] = true := by decide
theorem sweep_0275 : sameMembers (minimalVertices [1, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)))) [[true, false, false]] = true := by decide
theorem sweep_0276 : sameMembers (minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0277 : sameMembers (minimalVertices [0, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0278 : sameMembers (minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0279 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0280 : sameMembers (minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)))) [] = true := by decide
theorem sweep_0281 : sameMembers (minimalVertices [9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)))) [] = true := by decide
theorem sweep_0282 : sameMembers (minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)))) [[true], [true, false], [true, false, false], [true, true]] = true := by decide
theorem sweep_0283 : sameMembers (minimalVertices [1, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)))) [[true], [true, false], [true, false, false], [true, true]] = true := by decide
theorem sweep_0284 : sameMembers (minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, true]] = true := by decide
theorem sweep_0285 : sameMembers (minimalVertices [0, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, true]] = true := by decide
theorem sweep_0286 : sameMembers (minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0287 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0288 : sameMembers (minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)))) [] = true := by decide
theorem sweep_0289 : sameMembers (minimalVertices [9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)))) [] = true := by decide
theorem sweep_0290 : sameMembers (minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)))) [[true, false], [true, false, false], [true, false, true]] = true := by decide
theorem sweep_0291 : sameMembers (minimalVertices [1, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)))) [[true, false], [true, false, false], [true, false, true]] = true := by decide
theorem sweep_0292 : sameMembers (minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)))) [[], [false], [true], [true, true]] = true := by decide
theorem sweep_0293 : sameMembers (minimalVertices [0, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)))) [[], [false], [true], [true, true]] = true := by decide
theorem sweep_0294 : sameMembers (minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0295 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0296 : sameMembers (minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)))) [] = true := by decide
theorem sweep_0297 : sameMembers (minimalVertices [9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)))) [] = true := by decide
theorem sweep_0298 : sameMembers (minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)))) [[true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0299 : sameMembers (minimalVertices [1, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)))) [[true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0300 : sameMembers (minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)))) [[false]] = true := by decide
theorem sweep_0301 : sameMembers (minimalVertices [0, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)))) [[false]] = true := by decide
theorem sweep_0302 : sameMembers (minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0303 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0304 : sameMembers (minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))))) [] = true := by decide
theorem sweep_0305 : sameMembers (minimalVertices [9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))))) [] = true := by decide
theorem sweep_0306 : sameMembers (minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))))) [[false]] = true := by decide
theorem sweep_0307 : sameMembers (minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))))) [[false]] = true := by decide
theorem sweep_0308 : sameMembers (minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))))) [[true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0309 : sameMembers (minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))))) [[true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0310 : sameMembers (minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0311 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0312 : sameMembers (minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))))) [] = true := by decide
theorem sweep_0313 : sameMembers (minimalVertices [9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))))) [] = true := by decide
theorem sweep_0314 : sameMembers (minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))))) [[], [false], [true], [true, true], [true, true, true]] = true := by decide
theorem sweep_0315 : sameMembers (minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))))) [[], [false], [true], [true, true], [true, true, true]] = true := by decide
theorem sweep_0316 : sameMembers (minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))))) [[true], [true, false], [true, true], [true, true, false]] = true := by decide
theorem sweep_0317 : sameMembers (minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))))) [[true], [true, false], [true, true], [true, true, false]] = true := by decide
theorem sweep_0318 : sameMembers (minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0319 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0320 : sameMembers (minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))))) [] = true := by decide
theorem sweep_0321 : sameMembers (minimalVertices [9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))))) [] = true := by decide
theorem sweep_0322 : sameMembers (minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))))) [[], [false], [true], [true, true], [true, true, false]] = true := by decide
theorem sweep_0323 : sameMembers (minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))))) [[], [false], [true], [true, true], [true, true, false]] = true := by decide
theorem sweep_0324 : sameMembers (minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))))) [[true], [true, false], [true, true], [true, true, true]] = true := by decide
theorem sweep_0325 : sameMembers (minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))))) [[true], [true, false], [true, true], [true, true, true]] = true := by decide
theorem sweep_0326 : sameMembers (minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0327 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0328 : sameMembers (minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))))) [] = true := by decide
theorem sweep_0329 : sameMembers (minimalVertices [9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))))) [] = true := by decide
theorem sweep_0330 : sameMembers (minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))))) [[], [false], [true], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0331 : sameMembers (minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))))) [[], [false], [true], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0332 : sameMembers (minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))))) [[true, false]] = true := by decide
theorem sweep_0333 : sameMembers (minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))))) [[true, false]] = true := by decide
theorem sweep_0334 : sameMembers (minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0335 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0336 : sameMembers (minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))))) [] = true := by decide
theorem sweep_0337 : sameMembers (minimalVertices [9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))))) [] = true := by decide
theorem sweep_0338 : sameMembers (minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))))) [[], [false], [true], [true, false]] = true := by decide
theorem sweep_0339 : sameMembers (minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))))) [[], [false], [true], [true, false]] = true := by decide
theorem sweep_0340 : sameMembers (minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))))) [[true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0341 : sameMembers (minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))))) [[true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0342 : sameMembers (minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0343 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0344 : sameMembers (minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))))) [] = true := by decide
theorem sweep_0345 : sameMembers (minimalVertices [9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))))) [] = true := by decide
theorem sweep_0346 : sameMembers (minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))))) [[], [false], [true], [true, false], [true, true], [true, true, true]] = true := by decide
theorem sweep_0347 : sameMembers (minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))))) [[], [false], [true], [true, false], [true, true], [true, true, true]] = true := by decide
theorem sweep_0348 : sameMembers (minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))))) [[true, true, false]] = true := by decide
theorem sweep_0349 : sameMembers (minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))))) [[true, true, false]] = true := by decide
theorem sweep_0350 : sameMembers (minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0351 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0352 : sameMembers (minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))))) [] = true := by decide
theorem sweep_0353 : sameMembers (minimalVertices [9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))))) [] = true := by decide
theorem sweep_0354 : sameMembers (minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))))) [[], [false], [true], [true, false], [true, true], [true, true, false]] = true := by decide
theorem sweep_0355 : sameMembers (minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))))) [[], [false], [true], [true, false], [true, true], [true, true, false]] = true := by decide
theorem sweep_0356 : sameMembers (minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))))) [[true, true, true]] = true := by decide
theorem sweep_0357 : sameMembers (minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))))) [[true, true, true]] = true := by decide
theorem sweep_0358 : sameMembers (minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0359 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0360 : sameMembers (minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))))) [] = true := by decide
theorem sweep_0361 : sameMembers (minimalVertices [9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))))) [] = true := by decide
theorem sweep_0362 : sameMembers (minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0363 : sameMembers (minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0364 : sameMembers (minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))))) [] = true := by decide
theorem sweep_0365 : sameMembers (minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))))) [] = true := by decide
theorem sweep_0366 : sameMembers (minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0367 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))))) [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] = true := by decide
theorem sweep_0368 : sameMembers (minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)))) [] = true := by decide
theorem sweep_0369 : sameMembers (minimalVertices [9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)))) [] = true := by decide
theorem sweep_0370 : sameMembers (minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)))) [[false]] = true := by decide
theorem sweep_0371 : sameMembers (minimalVertices [1, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)))) [[false]] = true := by decide
theorem sweep_0372 : sameMembers (minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)))) [[true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0373 : sameMembers (minimalVertices [0, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)))) [[true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0374 : sameMembers (minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0375 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0376 : sameMembers (minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)))) [] = true := by decide
theorem sweep_0377 : sameMembers (minimalVertices [9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)))) [] = true := by decide
theorem sweep_0378 : sameMembers (minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)))) [[], [false], [true], [true, true]] = true := by decide
theorem sweep_0379 : sameMembers (minimalVertices [1, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)))) [[], [false], [true], [true, true]] = true := by decide
theorem sweep_0380 : sameMembers (minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)))) [[true, false], [true, false, false], [true, false, true]] = true := by decide
theorem sweep_0381 : sameMembers (minimalVertices [0, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)))) [[true, false], [true, false, false], [true, false, true]] = true := by decide
theorem sweep_0382 : sameMembers (minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0383 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0384 : sameMembers (minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)))) [] = true := by decide
theorem sweep_0385 : sameMembers (minimalVertices [9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)))) [] = true := by decide
theorem sweep_0386 : sameMembers (minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, true]] = true := by decide
theorem sweep_0387 : sameMembers (minimalVertices [1, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, true]] = true := by decide
theorem sweep_0388 : sameMembers (minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)))) [[true], [true, false], [true, false, false], [true, true]] = true := by decide
theorem sweep_0389 : sameMembers (minimalVertices [0, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)))) [[true], [true, false], [true, false, false], [true, true]] = true := by decide
theorem sweep_0390 : sameMembers (minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0391 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0392 : sameMembers (minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)))) [] = true := by decide
theorem sweep_0393 : sameMembers (minimalVertices [9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)))) [] = true := by decide
theorem sweep_0394 : sameMembers (minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0395 : sameMembers (minimalVertices [1, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0396 : sameMembers (minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)))) [[true, false, false]] = true := by decide
theorem sweep_0397 : sameMembers (minimalVertices [0, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)))) [[true, false, false]] = true := by decide
theorem sweep_0398 : sameMembers (minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0399 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0400 : sameMembers (minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)))) [] = true := by decide
theorem sweep_0401 : sameMembers (minimalVertices [9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)))) [] = true := by decide
theorem sweep_0402 : sameMembers (minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false]] = true := by decide
theorem sweep_0403 : sameMembers (minimalVertices [1, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false]] = true := by decide
theorem sweep_0404 : sameMembers (minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)))) [[true], [true, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0405 : sameMembers (minimalVertices [0, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)))) [[true], [true, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0406 : sameMembers (minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0407 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0408 : sameMembers (minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)))) [] = true := by decide
theorem sweep_0409 : sameMembers (minimalVertices [9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)))) [] = true := by decide
theorem sweep_0410 : sameMembers (minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false], [true, true]] = true := by decide
theorem sweep_0411 : sameMembers (minimalVertices [1, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false], [true, true]] = true := by decide
theorem sweep_0412 : sameMembers (minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)))) [[true, false, true]] = true := by decide
theorem sweep_0413 : sameMembers (minimalVertices [0, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)))) [[true, false, true]] = true := by decide
theorem sweep_0414 : sameMembers (minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0415 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0416 : sameMembers (minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)))) [] = true := by decide
theorem sweep_0417 : sameMembers (minimalVertices [9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)))) [] = true := by decide
theorem sweep_0418 : sameMembers (minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true]] = true := by decide
theorem sweep_0419 : sameMembers (minimalVertices [1, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true]] = true := by decide
theorem sweep_0420 : sameMembers (minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)))) [[true, true]] = true := by decide
theorem sweep_0421 : sameMembers (minimalVertices [0, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)))) [[true, true]] = true := by decide
theorem sweep_0422 : sameMembers (minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0423 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0424 : sameMembers (minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)))) [] = true := by decide
theorem sweep_0425 : sameMembers (minimalVertices [9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)))) [] = true := by decide
theorem sweep_0426 : sameMembers (minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0427 : sameMembers (minimalVertices [1, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0428 : sameMembers (minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)))) [] = true := by decide
theorem sweep_0429 : sameMembers (minimalVertices [0, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)))) [] = true := by decide
theorem sweep_0430 : sameMembers (minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0431 : sameMembers (minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)))) [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] = true := by decide
theorem sweep_0432 : sameMembers (minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) [] = true := by decide
theorem sweep_0433 : sameMembers (minimalVertices [9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) [] = true := by decide
theorem sweep_0434 : sameMembers (minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) [] = true := by decide
theorem sweep_0435 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) [] = true := by decide
theorem sweep_0436 : sameMembers (minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0437 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0438 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0439 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0440 : sameMembers (minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1)))) [] = true := by decide
theorem sweep_0441 : sameMembers (minimalVertices [9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1)))) [] = true := by decide
theorem sweep_0442 : sameMembers (minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1)))) [[true, true]] = true := by decide
theorem sweep_0443 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1)))) [[true, true]] = true := by decide
theorem sweep_0444 : sameMembers (minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1)))) [[], [false], [false, false], [false, true], [true], [true, false]] = true := by decide
theorem sweep_0445 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1)))) [[], [false], [false, false], [false, true], [true], [true, false]] = true := by decide
theorem sweep_0446 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0447 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0448 : sameMembers (minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0)))) [] = true := by decide
theorem sweep_0449 : sameMembers (minimalVertices [9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0)))) [] = true := by decide
theorem sweep_0450 : sameMembers (minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0)))) [[true, false]] = true := by decide
theorem sweep_0451 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0)))) [[true, false]] = true := by decide
theorem sweep_0452 : sameMembers (minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0)))) [[], [false], [false, false], [false, true], [true], [true, true]] = true := by decide
theorem sweep_0453 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0)))) [[], [false], [false, false], [false, true], [true], [true, true]] = true := by decide
theorem sweep_0454 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0455 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0456 : sameMembers (minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1)))) [] = true := by decide
theorem sweep_0457 : sameMembers (minimalVertices [9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1)))) [] = true := by decide
theorem sweep_0458 : sameMembers (minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1)))) [[true], [true, false], [true, true]] = true := by decide
theorem sweep_0459 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1)))) [[true], [true, false], [true, true]] = true := by decide
theorem sweep_0460 : sameMembers (minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1)))) [[false], [false, false], [false, true]] = true := by decide
theorem sweep_0461 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1)))) [[false], [false, false], [false, true]] = true := by decide
theorem sweep_0462 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0463 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0464 : sameMembers (minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0)))) [] = true := by decide
theorem sweep_0465 : sameMembers (minimalVertices [9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0)))) [] = true := by decide
theorem sweep_0466 : sameMembers (minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0)))) [[false, true]] = true := by decide
theorem sweep_0467 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0)))) [[false, true]] = true := by decide
theorem sweep_0468 : sameMembers (minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0)))) [[], [false], [false, false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0469 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0)))) [[], [false], [false, false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0470 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0471 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0472 : sameMembers (minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)))) [] = true := by decide
theorem sweep_0473 : sameMembers (minimalVertices [9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)))) [] = true := by decide
theorem sweep_0474 : sameMembers (minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)))) [[], [false], [false, true], [true], [true, true]] = true := by decide
theorem sweep_0475 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)))) [[], [false], [false, true], [true], [true, true]] = true := by decide
theorem sweep_0476 : sameMembers (minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)))) [[], [false], [false, false], [true], [true, false]] = true := by decide
theorem sweep_0477 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)))) [[], [false], [false, false], [true], [true, false]] = true := by decide
theorem sweep_0478 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0479 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0480 : sameMembers (minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0)))) [] = true := by decide
theorem sweep_0481 : sameMembers (minimalVertices [9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0)))) [] = true := by decide
theorem sweep_0482 : sameMembers (minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0)))) [[], [false], [false, true], [true], [true, false]] = true := by decide
theorem sweep_0483 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0)))) [[], [false], [false, true], [true], [true, false]] = true := by decide
theorem sweep_0484 : sameMembers (minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0)))) [[], [false], [false, false], [true], [true, true]] = true := by decide
theorem sweep_0485 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0)))) [[], [false], [false, false], [true], [true, true]] = true := by decide
theorem sweep_0486 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0487 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0488 : sameMembers (minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) [] = true := by decide
theorem sweep_0489 : sameMembers (minimalVertices [9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) [] = true := by decide
theorem sweep_0490 : sameMembers (minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) [[], [false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0491 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) [[], [false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0492 : sameMembers (minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) [[false, false]] = true := by decide
theorem sweep_0493 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) [[false, false]] = true := by decide
theorem sweep_0494 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0495 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0496 : sameMembers (minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) [] = true := by decide
theorem sweep_0497 : sameMembers (minimalVertices [9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) [] = true := by decide
theorem sweep_0498 : sameMembers (minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) [[false, false]] = true := by decide
theorem sweep_0499 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) [[false, false]] = true := by decide
theorem sweep_0500 : sameMembers (minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) [[], [false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0501 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) [[], [false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0502 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0503 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0504 : sameMembers (minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1)))) [] = true := by decide
theorem sweep_0505 : sameMembers (minimalVertices [9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1)))) [] = true := by decide
theorem sweep_0506 : sameMembers (minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1)))) [[], [false], [false, false], [true], [true, true]] = true := by decide
theorem sweep_0507 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1)))) [[], [false], [false, false], [true], [true, true]] = true := by decide
theorem sweep_0508 : sameMembers (minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1)))) [[], [false], [false, true], [true], [true, false]] = true := by decide
theorem sweep_0509 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1)))) [[], [false], [false, true], [true], [true, false]] = true := by decide
theorem sweep_0510 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0511 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0512 : sameMembers (minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0)))) [] = true := by decide
theorem sweep_0513 : sameMembers (minimalVertices [9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0)))) [] = true := by decide
theorem sweep_0514 : sameMembers (minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0)))) [[], [false], [false, false], [true], [true, false]] = true := by decide
theorem sweep_0515 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0)))) [[], [false], [false, false], [true], [true, false]] = true := by decide
theorem sweep_0516 : sameMembers (minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0)))) [[], [false], [false, true], [true], [true, true]] = true := by decide
theorem sweep_0517 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0)))) [[], [false], [false, true], [true], [true, true]] = true := by decide
theorem sweep_0518 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0519 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0520 : sameMembers (minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1)))) [] = true := by decide
theorem sweep_0521 : sameMembers (minimalVertices [9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1)))) [] = true := by decide
theorem sweep_0522 : sameMembers (minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1)))) [[], [false], [false, false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0523 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1)))) [[], [false], [false, false], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0524 : sameMembers (minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1)))) [[false, true]] = true := by decide
theorem sweep_0525 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1)))) [[false, true]] = true := by decide
theorem sweep_0526 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0527 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0528 : sameMembers (minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0)))) [] = true := by decide
theorem sweep_0529 : sameMembers (minimalVertices [9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0)))) [] = true := by decide
theorem sweep_0530 : sameMembers (minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0)))) [[false], [false, false], [false, true]] = true := by decide
theorem sweep_0531 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0)))) [[false], [false, false], [false, true]] = true := by decide
theorem sweep_0532 : sameMembers (minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0)))) [[true], [true, false], [true, true]] = true := by decide
theorem sweep_0533 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0)))) [[true], [true, false], [true, true]] = true := by decide
theorem sweep_0534 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0535 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0536 : sameMembers (minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1)))) [] = true := by decide
theorem sweep_0537 : sameMembers (minimalVertices [9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1)))) [] = true := by decide
theorem sweep_0538 : sameMembers (minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1)))) [[], [false], [false, false], [false, true], [true], [true, true]] = true := by decide
theorem sweep_0539 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1)))) [[], [false], [false, false], [false, true], [true], [true, true]] = true := by decide
theorem sweep_0540 : sameMembers (minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1)))) [[true, false]] = true := by decide
theorem sweep_0541 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1)))) [[true, false]] = true := by decide
theorem sweep_0542 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0543 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0544 : sameMembers (minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0)))) [] = true := by decide
theorem sweep_0545 : sameMembers (minimalVertices [9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0)))) [] = true := by decide
theorem sweep_0546 : sameMembers (minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0)))) [[], [false], [false, false], [false, true], [true], [true, false]] = true := by decide
theorem sweep_0547 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0)))) [[], [false], [false, false], [false, true], [true], [true, false]] = true := by decide
theorem sweep_0548 : sameMembers (minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0)))) [[true, true]] = true := by decide
theorem sweep_0549 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0)))) [[true, true]] = true := by decide
theorem sweep_0550 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0551 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0552 : sameMembers (minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) [] = true := by decide
theorem sweep_0553 : sameMembers (minimalVertices [9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) [] = true := by decide
theorem sweep_0554 : sameMembers (minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0555 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0556 : sameMembers (minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) [] = true := by decide
theorem sweep_0557 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) [] = true := by decide
theorem sweep_0558 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0559 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] = true := by decide
theorem sweep_0560 : sameMembers (minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0))) [] = true := by decide
theorem sweep_0561 : sameMembers (minimalVertices [9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0))) [] = true := by decide
theorem sweep_0562 : sameMembers (minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0))) [] = true := by decide
theorem sweep_0563 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0))) [] = true := by decide
theorem sweep_0564 : sameMembers (minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0565 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0566 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0567 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0568 : sameMembers (minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1))) [] = true := by decide
theorem sweep_0569 : sameMembers (minimalVertices [9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1))) [] = true := by decide
theorem sweep_0570 : sameMembers (minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1))) [[true]] = true := by decide
theorem sweep_0571 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1))) [[true]] = true := by decide
theorem sweep_0572 : sameMembers (minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1))) [[false], [false, false], [false, true], [false, true, false], [false, true, true]] = true := by decide
theorem sweep_0573 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1))) [[false], [false, false], [false, true], [false, true, false], [false, true, true]] = true := by decide
theorem sweep_0574 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0575 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0576 : sameMembers (minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0))) [] = true := by decide
theorem sweep_0577 : sameMembers (minimalVertices [9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0))) [] = true := by decide
theorem sweep_0578 : sameMembers (minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0))) [[false, true, true]] = true := by decide
theorem sweep_0579 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0))) [[false, true, true]] = true := by decide
theorem sweep_0580 : sameMembers (minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0))) [[], [false], [false, false], [false, true], [false, true, false], [true]] = true := by decide
theorem sweep_0581 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0))) [[], [false], [false, false], [false, true], [false, true, false], [true]] = true := by decide
theorem sweep_0582 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0583 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0584 : sameMembers (minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1))) [] = true := by decide
theorem sweep_0585 : sameMembers (minimalVertices [9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1))) [] = true := by decide
theorem sweep_0586 : sameMembers (minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1))) [[], [false], [false, true], [false, true, true], [true]] = true := by decide
theorem sweep_0587 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1))) [[], [false], [false, true], [false, true, true], [true]] = true := by decide
theorem sweep_0588 : sameMembers (minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1))) [[false], [false, false], [false, true], [false, true, false]] = true := by decide
theorem sweep_0589 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1))) [[false], [false, false], [false, true], [false, true, false]] = true := by decide
theorem sweep_0590 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0591 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0592 : sameMembers (minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0))) [] = true := by decide
theorem sweep_0593 : sameMembers (minimalVertices [9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0))) [] = true := by decide
theorem sweep_0594 : sameMembers (minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0))) [[false, true, false]] = true := by decide
theorem sweep_0595 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0))) [[false, true, false]] = true := by decide
theorem sweep_0596 : sameMembers (minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0))) [[], [false], [false, false], [false, true], [false, true, true], [true]] = true := by decide
theorem sweep_0597 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0))) [[], [false], [false, false], [false, true], [false, true, true], [true]] = true := by decide
theorem sweep_0598 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0599 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0600 : sameMembers (minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1))) [] = true := by decide
theorem sweep_0601 : sameMembers (minimalVertices [9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1))) [] = true := by decide
theorem sweep_0602 : sameMembers (minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1))) [[], [false], [false, true], [false, true, false], [true]] = true := by decide
theorem sweep_0603 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1))) [[], [false], [false, true], [false, true, false], [true]] = true := by decide
theorem sweep_0604 : sameMembers (minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1))) [[false], [false, false], [false, true], [false, true, true]] = true := by decide
theorem sweep_0605 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1))) [[false], [false, false], [false, true], [false, true, true]] = true := by decide
theorem sweep_0606 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0607 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0608 : sameMembers (minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0))) [] = true := by decide
theorem sweep_0609 : sameMembers (minimalVertices [9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0))) [] = true := by decide
theorem sweep_0610 : sameMembers (minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0))) [[false, true], [false, true, false], [false, true, true]] = true := by decide
theorem sweep_0611 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0))) [[false, true], [false, true, false], [false, true, true]] = true := by decide
theorem sweep_0612 : sameMembers (minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0))) [[], [false], [false, false], [true]] = true := by decide
theorem sweep_0613 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0))) [[], [false], [false, false], [true]] = true := by decide
theorem sweep_0614 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0615 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0616 : sameMembers (minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1))) [] = true := by decide
theorem sweep_0617 : sameMembers (minimalVertices [9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1))) [] = true := by decide
theorem sweep_0618 : sameMembers (minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1))) [[], [false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0619 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1))) [[], [false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0620 : sameMembers (minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1))) [[false, false]] = true := by decide
theorem sweep_0621 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1))) [[false, false]] = true := by decide
theorem sweep_0622 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0623 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0624 : sameMembers (minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0))) [] = true := by decide
theorem sweep_0625 : sameMembers (minimalVertices [9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0))) [] = true := by decide
theorem sweep_0626 : sameMembers (minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0))) [[false, false]] = true := by decide
theorem sweep_0627 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0))) [[false, false]] = true := by decide
theorem sweep_0628 : sameMembers (minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0))) [[], [false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0629 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0))) [[], [false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0630 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0631 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0632 : sameMembers (minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1))) [] = true := by decide
theorem sweep_0633 : sameMembers (minimalVertices [9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1))) [] = true := by decide
theorem sweep_0634 : sameMembers (minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1))) [[], [false], [false, false], [true]] = true := by decide
theorem sweep_0635 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1))) [[], [false], [false, false], [true]] = true := by decide
theorem sweep_0636 : sameMembers (minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1))) [[false, true], [false, true, false], [false, true, true]] = true := by decide
theorem sweep_0637 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1))) [[false, true], [false, true, false], [false, true, true]] = true := by decide
theorem sweep_0638 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0639 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0640 : sameMembers (minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0))) [] = true := by decide
theorem sweep_0641 : sameMembers (minimalVertices [9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0))) [] = true := by decide
theorem sweep_0642 : sameMembers (minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0))) [[false], [false, false], [false, true], [false, true, true]] = true := by decide
theorem sweep_0643 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0))) [[false], [false, false], [false, true], [false, true, true]] = true := by decide
theorem sweep_0644 : sameMembers (minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0))) [[], [false], [false, true], [false, true, false], [true]] = true := by decide
theorem sweep_0645 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0))) [[], [false], [false, true], [false, true, false], [true]] = true := by decide
theorem sweep_0646 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0647 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0648 : sameMembers (minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1))) [] = true := by decide
theorem sweep_0649 : sameMembers (minimalVertices [9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1))) [] = true := by decide
theorem sweep_0650 : sameMembers (minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1))) [[], [false], [false, false], [false, true], [false, true, true], [true]] = true := by decide
theorem sweep_0651 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1))) [[], [false], [false, false], [false, true], [false, true, true], [true]] = true := by decide
theorem sweep_0652 : sameMembers (minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1))) [[false, true, false]] = true := by decide
theorem sweep_0653 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1))) [[false, true, false]] = true := by decide
theorem sweep_0654 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0655 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0656 : sameMembers (minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0))) [] = true := by decide
theorem sweep_0657 : sameMembers (minimalVertices [9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0))) [] = true := by decide
theorem sweep_0658 : sameMembers (minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0))) [[false], [false, false], [false, true], [false, true, false]] = true := by decide
theorem sweep_0659 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0))) [[false], [false, false], [false, true], [false, true, false]] = true := by decide
theorem sweep_0660 : sameMembers (minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0))) [[], [false], [false, true], [false, true, true], [true]] = true := by decide
theorem sweep_0661 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0))) [[], [false], [false, true], [false, true, true], [true]] = true := by decide
theorem sweep_0662 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0663 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0664 : sameMembers (minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1))) [] = true := by decide
theorem sweep_0665 : sameMembers (minimalVertices [9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1))) [] = true := by decide
theorem sweep_0666 : sameMembers (minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1))) [[], [false], [false, false], [false, true], [false, true, false], [true]] = true := by decide
theorem sweep_0667 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1))) [[], [false], [false, false], [false, true], [false, true, false], [true]] = true := by decide
theorem sweep_0668 : sameMembers (minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1))) [[false, true, true]] = true := by decide
theorem sweep_0669 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1))) [[false, true, true]] = true := by decide
theorem sweep_0670 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0671 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0672 : sameMembers (minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0))) [] = true := by decide
theorem sweep_0673 : sameMembers (minimalVertices [9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0))) [] = true := by decide
theorem sweep_0674 : sameMembers (minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0))) [[false], [false, false], [false, true], [false, true, false], [false, true, true]] = true := by decide
theorem sweep_0675 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0))) [[false], [false, false], [false, true], [false, true, false], [false, true, true]] = true := by decide
theorem sweep_0676 : sameMembers (minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0))) [[true]] = true := by decide
theorem sweep_0677 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0))) [[true]] = true := by decide
theorem sweep_0678 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0679 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0680 : sameMembers (minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1))) [] = true := by decide
theorem sweep_0681 : sameMembers (minimalVertices [9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1))) [] = true := by decide
theorem sweep_0682 : sameMembers (minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0683 : sameMembers (minimalVertices [1, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0684 : sameMembers (minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1))) [] = true := by decide
theorem sweep_0685 : sameMembers (minimalVertices [0, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1))) [] = true := by decide
theorem sweep_0686 : sameMembers (minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0687 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1))) [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] = true := by decide
theorem sweep_0688 : sameMembers (minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0))) [] = true := by decide
theorem sweep_0689 : sameMembers (minimalVertices [9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0))) [] = true := by decide
theorem sweep_0690 : sameMembers (minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0))) [] = true := by decide
theorem sweep_0691 : sameMembers (minimalVertices [1, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0))) [] = true := by decide
theorem sweep_0692 : sameMembers (minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0693 : sameMembers (minimalVertices [0, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0694 : sameMembers (minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0695 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0696 : sameMembers (minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1))) [] = true := by decide
theorem sweep_0697 : sameMembers (minimalVertices [9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1))) [] = true := by decide
theorem sweep_0698 : sameMembers (minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1))) [[true]] = true := by decide
theorem sweep_0699 : sameMembers (minimalVertices [1, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1))) [[true]] = true := by decide
theorem sweep_0700 : sameMembers (minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1))) [[false], [false, false], [false, false, false], [false, false, true], [false, true]] = true := by decide
theorem sweep_0701 : sameMembers (minimalVertices [0, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1))) [[false], [false, false], [false, false, false], [false, false, true], [false, true]] = true := by decide
theorem sweep_0702 : sameMembers (minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0703 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0704 : sameMembers (minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0))) [] = true := by decide
theorem sweep_0705 : sameMembers (minimalVertices [9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0))) [] = true := by decide
theorem sweep_0706 : sameMembers (minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0))) [[false, true]] = true := by decide
theorem sweep_0707 : sameMembers (minimalVertices [1, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0))) [[false, true]] = true := by decide
theorem sweep_0708 : sameMembers (minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [false, false, true], [true]] = true := by decide
theorem sweep_0709 : sameMembers (minimalVertices [0, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [false, false, true], [true]] = true := by decide
theorem sweep_0710 : sameMembers (minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0711 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0712 : sameMembers (minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1))) [] = true := by decide
theorem sweep_0713 : sameMembers (minimalVertices [9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1))) [] = true := by decide
theorem sweep_0714 : sameMembers (minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1))) [[], [false], [false, true], [true]] = true := by decide
theorem sweep_0715 : sameMembers (minimalVertices [1, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1))) [[], [false], [false, true], [true]] = true := by decide
theorem sweep_0716 : sameMembers (minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1))) [[false, false], [false, false, false], [false, false, true]] = true := by decide
theorem sweep_0717 : sameMembers (minimalVertices [0, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1))) [[false, false], [false, false, false], [false, false, true]] = true := by decide
theorem sweep_0718 : sameMembers (minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0719 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0720 : sameMembers (minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0))) [] = true := by decide
theorem sweep_0721 : sameMembers (minimalVertices [9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0))) [] = true := by decide
theorem sweep_0722 : sameMembers (minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0))) [[false, false, true]] = true := by decide
theorem sweep_0723 : sameMembers (minimalVertices [1, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0))) [[false, false, true]] = true := by decide
theorem sweep_0724 : sameMembers (minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [false, true], [true]] = true := by decide
theorem sweep_0725 : sameMembers (minimalVertices [0, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [false, true], [true]] = true := by decide
theorem sweep_0726 : sameMembers (minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0727 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0728 : sameMembers (minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1))) [] = true := by decide
theorem sweep_0729 : sameMembers (minimalVertices [9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1))) [] = true := by decide
theorem sweep_0730 : sameMembers (minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1))) [[], [false], [false, false], [false, false, true], [true]] = true := by decide
theorem sweep_0731 : sameMembers (minimalVertices [1, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1))) [[], [false], [false, false], [false, false, true], [true]] = true := by decide
theorem sweep_0732 : sameMembers (minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1))) [[false], [false, false], [false, false, false], [false, true]] = true := by decide
theorem sweep_0733 : sameMembers (minimalVertices [0, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1))) [[false], [false, false], [false, false, false], [false, true]] = true := by decide
theorem sweep_0734 : sameMembers (minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0735 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0736 : sameMembers (minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0))) [] = true := by decide
theorem sweep_0737 : sameMembers (minimalVertices [9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0))) [] = true := by decide
theorem sweep_0738 : sameMembers (minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0))) [[false], [false, false], [false, false, true], [false, true]] = true := by decide
theorem sweep_0739 : sameMembers (minimalVertices [1, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0))) [[false], [false, false], [false, false, true], [false, true]] = true := by decide
theorem sweep_0740 : sameMembers (minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [true]] = true := by decide
theorem sweep_0741 : sameMembers (minimalVertices [0, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [true]] = true := by decide
theorem sweep_0742 : sameMembers (minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0743 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0744 : sameMembers (minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1))) [] = true := by decide
theorem sweep_0745 : sameMembers (minimalVertices [9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1))) [] = true := by decide
theorem sweep_0746 : sameMembers (minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1))) [[], [false], [false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0747 : sameMembers (minimalVertices [1, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1))) [[], [false], [false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0748 : sameMembers (minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1))) [[false, false, false]] = true := by decide
theorem sweep_0749 : sameMembers (minimalVertices [0, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1))) [[false, false, false]] = true := by decide
theorem sweep_0750 : sameMembers (minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0751 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0752 : sameMembers (minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0))) [] = true := by decide
theorem sweep_0753 : sameMembers (minimalVertices [9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0))) [] = true := by decide
theorem sweep_0754 : sameMembers (minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0))) [[false, false, false]] = true := by decide
theorem sweep_0755 : sameMembers (minimalVertices [1, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0))) [[false, false, false]] = true := by decide
theorem sweep_0756 : sameMembers (minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0))) [[], [false], [false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0757 : sameMembers (minimalVertices [0, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0))) [[], [false], [false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0758 : sameMembers (minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0759 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0760 : sameMembers (minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1))) [] = true := by decide
theorem sweep_0761 : sameMembers (minimalVertices [9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1))) [] = true := by decide
theorem sweep_0762 : sameMembers (minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [true]] = true := by decide
theorem sweep_0763 : sameMembers (minimalVertices [1, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [true]] = true := by decide
theorem sweep_0764 : sameMembers (minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1))) [[false], [false, false], [false, false, true], [false, true]] = true := by decide
theorem sweep_0765 : sameMembers (minimalVertices [0, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1))) [[false], [false, false], [false, false, true], [false, true]] = true := by decide
theorem sweep_0766 : sameMembers (minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0767 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0768 : sameMembers (minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0))) [] = true := by decide
theorem sweep_0769 : sameMembers (minimalVertices [9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0))) [] = true := by decide
theorem sweep_0770 : sameMembers (minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0))) [[false], [false, false], [false, false, false], [false, true]] = true := by decide
theorem sweep_0771 : sameMembers (minimalVertices [1, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0))) [[false], [false, false], [false, false, false], [false, true]] = true := by decide
theorem sweep_0772 : sameMembers (minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0))) [[], [false], [false, false], [false, false, true], [true]] = true := by decide
theorem sweep_0773 : sameMembers (minimalVertices [0, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0))) [[], [false], [false, false], [false, false, true], [true]] = true := by decide
theorem sweep_0774 : sameMembers (minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0775 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0776 : sameMembers (minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1))) [] = true := by decide
theorem sweep_0777 : sameMembers (minimalVertices [9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1))) [] = true := by decide
theorem sweep_0778 : sameMembers (minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [false, true], [true]] = true := by decide
theorem sweep_0779 : sameMembers (minimalVertices [1, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [false, true], [true]] = true := by decide
theorem sweep_0780 : sameMembers (minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1))) [[false, false, true]] = true := by decide
theorem sweep_0781 : sameMembers (minimalVertices [0, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1))) [[false, false, true]] = true := by decide
theorem sweep_0782 : sameMembers (minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0783 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0784 : sameMembers (minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0))) [] = true := by decide
theorem sweep_0785 : sameMembers (minimalVertices [9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0))) [] = true := by decide
theorem sweep_0786 : sameMembers (minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0))) [[false, false], [false, false, false], [false, false, true]] = true := by decide
theorem sweep_0787 : sameMembers (minimalVertices [1, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0))) [[false, false], [false, false, false], [false, false, true]] = true := by decide
theorem sweep_0788 : sameMembers (minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0))) [[], [false], [false, true], [true]] = true := by decide
theorem sweep_0789 : sameMembers (minimalVertices [0, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0))) [[], [false], [false, true], [true]] = true := by decide
theorem sweep_0790 : sameMembers (minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0791 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0792 : sameMembers (minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1))) [] = true := by decide
theorem sweep_0793 : sameMembers (minimalVertices [9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1))) [] = true := by decide
theorem sweep_0794 : sameMembers (minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [false, false, true], [true]] = true := by decide
theorem sweep_0795 : sameMembers (minimalVertices [1, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [false, false, true], [true]] = true := by decide
theorem sweep_0796 : sameMembers (minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1))) [[false, true]] = true := by decide
theorem sweep_0797 : sameMembers (minimalVertices [0, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1))) [[false, true]] = true := by decide
theorem sweep_0798 : sameMembers (minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0799 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0800 : sameMembers (minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0))) [] = true := by decide
theorem sweep_0801 : sameMembers (minimalVertices [9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0))) [] = true := by decide
theorem sweep_0802 : sameMembers (minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0))) [[false], [false, false], [false, false, false], [false, false, true], [false, true]] = true := by decide
theorem sweep_0803 : sameMembers (minimalVertices [1, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0))) [[false], [false, false], [false, false, false], [false, false, true], [false, true]] = true := by decide
theorem sweep_0804 : sameMembers (minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0))) [[true]] = true := by decide
theorem sweep_0805 : sameMembers (minimalVertices [0, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0))) [[true]] = true := by decide
theorem sweep_0806 : sameMembers (minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0807 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0808 : sameMembers (minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1))) [] = true := by decide
theorem sweep_0809 : sameMembers (minimalVertices [9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1))) [] = true := by decide
theorem sweep_0810 : sameMembers (minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0811 : sameMembers (minimalVertices [1, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0812 : sameMembers (minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1))) [] = true := by decide
theorem sweep_0813 : sameMembers (minimalVertices [0, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1))) [] = true := by decide
theorem sweep_0814 : sameMembers (minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide
theorem sweep_0815 : sameMembers (minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1))) [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] = true := by decide

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
#print axioms sweep_0815
end PrefixRouteFinite
