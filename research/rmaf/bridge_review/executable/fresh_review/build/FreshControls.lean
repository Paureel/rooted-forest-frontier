import ExecutableConnectivity
open RMAF BridgeReview ExecutableBridge
namespace FreshExecutableReview
set_option maxRecDepth 10000
theorem hand_empty : minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) = [] := by decide
theorem hand_absent : minimalVertices [9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) = [] := by decide
theorem hand_singleton : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) = [[false,true]] := by decide
theorem hand_branching : minimalVertices [0, 2] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) = [[],[false],[false,false],[true],[true,false]] := by decide
theorem hand_one_suppressed : minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) = [[false],[false,false],[false,true]] := by decide
theorem hand_leaf_present : minimalVertices [7] (.leaf 7) = [[]] := by decide
theorem hand_leaf_absent : minimalVertices [8] (.leaf 7) = [] := by decide
theorem hand_duplicate_labels : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 2) (.leaf 3))) = [[false],[false,false],[false,true]] := by decide
theorem hand_two_suppressed : minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 3)) = [[false,false],[false,false,false],[false,false,true]] := by decide
theorem finite_0 : minimalVertices [] (.leaf 0) = [] := by decide
theorem finite_1 : minimalVertices [0] (.leaf 0) = [[]] := by decide
theorem finite_2 : minimalVertices [1] (.leaf 0) = [] := by decide
theorem finite_3 : minimalVertices [9] (.leaf 0) = [] := by decide
theorem finite_4 : minimalVertices [0, 1] (.leaf 0) = [[]] := by decide
theorem finite_5 : minimalVertices [0, 9] (.leaf 0) = [[]] := by decide
theorem finite_6 : minimalVertices [1, 9] (.leaf 0) = [] := by decide
theorem finite_7 : minimalVertices [0, 1, 9] (.leaf 0) = [[]] := by decide
theorem finite_8 : minimalVertices [] (.leaf 1) = [] := by decide
theorem finite_9 : minimalVertices [0] (.leaf 1) = [] := by decide
theorem finite_10 : minimalVertices [1] (.leaf 1) = [[]] := by decide
theorem finite_11 : minimalVertices [9] (.leaf 1) = [] := by decide
theorem finite_12 : minimalVertices [0, 1] (.leaf 1) = [[]] := by decide
theorem finite_13 : minimalVertices [0, 9] (.leaf 1) = [] := by decide
theorem finite_14 : minimalVertices [1, 9] (.leaf 1) = [[]] := by decide
theorem finite_15 : minimalVertices [0, 1, 9] (.leaf 1) = [[]] := by decide
theorem finite_16 : minimalVertices [] (.node (.leaf 0) (.leaf 0)) = [] := by decide
theorem finite_17 : minimalVertices [0] (.node (.leaf 0) (.leaf 0)) = [[],[false],[true]] := by decide
theorem finite_18 : minimalVertices [1] (.node (.leaf 0) (.leaf 0)) = [] := by decide
theorem finite_19 : minimalVertices [9] (.node (.leaf 0) (.leaf 0)) = [] := by decide
theorem finite_20 : minimalVertices [0, 1] (.node (.leaf 0) (.leaf 0)) = [[],[false],[true]] := by decide
theorem finite_21 : minimalVertices [0, 9] (.node (.leaf 0) (.leaf 0)) = [[],[false],[true]] := by decide
theorem finite_22 : minimalVertices [1, 9] (.node (.leaf 0) (.leaf 0)) = [] := by decide
theorem finite_23 : minimalVertices [0, 1, 9] (.node (.leaf 0) (.leaf 0)) = [[],[false],[true]] := by decide
theorem finite_24 : minimalVertices [] (.node (.leaf 0) (.leaf 1)) = [] := by decide
theorem finite_25 : minimalVertices [0] (.node (.leaf 0) (.leaf 1)) = [[false]] := by decide
theorem finite_26 : minimalVertices [1] (.node (.leaf 0) (.leaf 1)) = [[true]] := by decide
theorem finite_27 : minimalVertices [9] (.node (.leaf 0) (.leaf 1)) = [] := by decide
theorem finite_28 : minimalVertices [0, 1] (.node (.leaf 0) (.leaf 1)) = [[],[false],[true]] := by decide
theorem finite_29 : minimalVertices [0, 9] (.node (.leaf 0) (.leaf 1)) = [[false]] := by decide
theorem finite_30 : minimalVertices [1, 9] (.node (.leaf 0) (.leaf 1)) = [[true]] := by decide
theorem finite_31 : minimalVertices [0, 1, 9] (.node (.leaf 0) (.leaf 1)) = [[],[false],[true]] := by decide
theorem finite_32 : minimalVertices [] (.node (.leaf 1) (.leaf 0)) = [] := by decide
theorem finite_33 : minimalVertices [0] (.node (.leaf 1) (.leaf 0)) = [[true]] := by decide
theorem finite_34 : minimalVertices [1] (.node (.leaf 1) (.leaf 0)) = [[false]] := by decide
theorem finite_35 : minimalVertices [9] (.node (.leaf 1) (.leaf 0)) = [] := by decide
theorem finite_36 : minimalVertices [0, 1] (.node (.leaf 1) (.leaf 0)) = [[],[false],[true]] := by decide
theorem finite_37 : minimalVertices [0, 9] (.node (.leaf 1) (.leaf 0)) = [[true]] := by decide
theorem finite_38 : minimalVertices [1, 9] (.node (.leaf 1) (.leaf 0)) = [[false]] := by decide
theorem finite_39 : minimalVertices [0, 1, 9] (.node (.leaf 1) (.leaf 0)) = [[],[false],[true]] := by decide
theorem finite_40 : minimalVertices [] (.node (.leaf 1) (.leaf 1)) = [] := by decide
theorem finite_41 : minimalVertices [0] (.node (.leaf 1) (.leaf 1)) = [] := by decide
theorem finite_42 : minimalVertices [1] (.node (.leaf 1) (.leaf 1)) = [[],[false],[true]] := by decide
theorem finite_43 : minimalVertices [9] (.node (.leaf 1) (.leaf 1)) = [] := by decide
theorem finite_44 : minimalVertices [0, 1] (.node (.leaf 1) (.leaf 1)) = [[],[false],[true]] := by decide
theorem finite_45 : minimalVertices [0, 9] (.node (.leaf 1) (.leaf 1)) = [] := by decide
theorem finite_46 : minimalVertices [1, 9] (.node (.leaf 1) (.leaf 1)) = [[],[false],[true]] := by decide
theorem finite_47 : minimalVertices [0, 1, 9] (.node (.leaf 1) (.leaf 1)) = [[],[false],[true]] := by decide
theorem finite_48 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [] := by decide
theorem finite_49 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [[],[false],[true],[true,false],[true,true]] := by decide
theorem finite_50 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [] := by decide
theorem finite_51 : minimalVertices [9] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [] := by decide
theorem finite_52 : minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [[],[false],[true],[true,false],[true,true]] := by decide
theorem finite_53 : minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [[],[false],[true],[true,false],[true,true]] := by decide
theorem finite_54 : minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [] := by decide
theorem finite_55 : minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [[],[false],[true],[true,false],[true,true]] := by decide
theorem finite_56 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [] := by decide
theorem finite_57 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [[],[false],[true],[true,false]] := by decide
theorem finite_58 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [[true,true]] := by decide
theorem finite_59 : minimalVertices [9] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [] := by decide
theorem finite_60 : minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [[],[false],[true],[true,false],[true,true]] := by decide
theorem finite_61 : minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [[],[false],[true],[true,false]] := by decide
theorem finite_62 : minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [[true,true]] := by decide
theorem finite_63 : minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [[],[false],[true],[true,false],[true,true]] := by decide
theorem finite_64 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [] := by decide
theorem finite_65 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [[],[false],[true],[true,true]] := by decide
theorem finite_66 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [[true,false]] := by decide
theorem finite_67 : minimalVertices [9] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [] := by decide
theorem finite_68 : minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [[],[false],[true],[true,false],[true,true]] := by decide
theorem finite_69 : minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [[],[false],[true],[true,true]] := by decide
theorem finite_70 : minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [[true,false]] := by decide
theorem finite_71 : minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [[],[false],[true],[true,false],[true,true]] := by decide
theorem finite_72 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [] := by decide
theorem finite_73 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [[false]] := by decide
theorem finite_74 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [[true],[true,false],[true,true]] := by decide
theorem finite_75 : minimalVertices [9] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [] := by decide
theorem finite_76 : minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [[],[false],[true],[true,false],[true,true]] := by decide
theorem finite_77 : minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [[false]] := by decide
theorem finite_78 : minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [[true],[true,false],[true,true]] := by decide
theorem finite_79 : minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [[],[false],[true],[true,false],[true,true]] := by decide
theorem finite_80 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [] := by decide
theorem finite_81 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [[true],[true,false],[true,true]] := by decide
theorem finite_82 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [[false]] := by decide
theorem finite_83 : minimalVertices [9] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [] := by decide
theorem finite_84 : minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [[],[false],[true],[true,false],[true,true]] := by decide
theorem finite_85 : minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [[true],[true,false],[true,true]] := by decide
theorem finite_86 : minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [[false]] := by decide
theorem finite_87 : minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [[],[false],[true],[true,false],[true,true]] := by decide
theorem finite_88 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [] := by decide
theorem finite_89 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [[true,false]] := by decide
theorem finite_90 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [[],[false],[true],[true,true]] := by decide
theorem finite_91 : minimalVertices [9] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [] := by decide
theorem finite_92 : minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [[],[false],[true],[true,false],[true,true]] := by decide
theorem finite_93 : minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [[true,false]] := by decide
theorem finite_94 : minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [[],[false],[true],[true,true]] := by decide
theorem finite_95 : minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [[],[false],[true],[true,false],[true,true]] := by decide
theorem finite_96 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [] := by decide
theorem finite_97 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [[true,true]] := by decide
theorem finite_98 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [[],[false],[true],[true,false]] := by decide
theorem finite_99 : minimalVertices [9] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [] := by decide
theorem finite_100 : minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [[],[false],[true],[true,false],[true,true]] := by decide
theorem finite_101 : minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [[true,true]] := by decide
theorem finite_102 : minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [[],[false],[true],[true,false]] := by decide
theorem finite_103 : minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [[],[false],[true],[true,false],[true,true]] := by decide
theorem finite_104 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [] := by decide
theorem finite_105 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [] := by decide
theorem finite_106 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [[],[false],[true],[true,false],[true,true]] := by decide
theorem finite_107 : minimalVertices [9] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [] := by decide
theorem finite_108 : minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [[],[false],[true],[true,false],[true,true]] := by decide
theorem finite_109 : minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [] := by decide
theorem finite_110 : minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [[],[false],[true],[true,false],[true,true]] := by decide
theorem finite_111 : minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [[],[false],[true],[true,false],[true,true]] := by decide
theorem finite_112 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [] := by decide
theorem finite_113 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,true],[true]] := by decide
theorem finite_114 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [] := by decide
theorem finite_115 : minimalVertices [9] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [] := by decide
theorem finite_116 : minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,true],[true]] := by decide
theorem finite_117 : minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,true],[true]] := by decide
theorem finite_118 : minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [] := by decide
theorem finite_119 : minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,true],[true]] := by decide
theorem finite_120 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [] := by decide
theorem finite_121 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [[false],[false,false],[false,true]] := by decide
theorem finite_122 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [[true]] := by decide
theorem finite_123 : minimalVertices [9] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [] := by decide
theorem finite_124 : minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,true],[true]] := by decide
theorem finite_125 : minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [[false],[false,false],[false,true]] := by decide
theorem finite_126 : minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [[true]] := by decide
theorem finite_127 : minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,true],[true]] := by decide
theorem finite_128 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [] := by decide
theorem finite_129 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[true]] := by decide
theorem finite_130 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [[false,true]] := by decide
theorem finite_131 : minimalVertices [9] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [] := by decide
theorem finite_132 : minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,true],[true]] := by decide
theorem finite_133 : minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[true]] := by decide
theorem finite_134 : minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [[false,true]] := by decide
theorem finite_135 : minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,true],[true]] := by decide
theorem finite_136 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [] := by decide
theorem finite_137 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [[false,false]] := by decide
theorem finite_138 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [[],[false],[false,true],[true]] := by decide
theorem finite_139 : minimalVertices [9] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [] := by decide
theorem finite_140 : minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,true],[true]] := by decide
theorem finite_141 : minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [[false,false]] := by decide
theorem finite_142 : minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [[],[false],[false,true],[true]] := by decide
theorem finite_143 : minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,true],[true]] := by decide
theorem finite_144 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [] := by decide
theorem finite_145 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [[],[false],[false,true],[true]] := by decide
theorem finite_146 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [[false,false]] := by decide
theorem finite_147 : minimalVertices [9] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [] := by decide
theorem finite_148 : minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,true],[true]] := by decide
theorem finite_149 : minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [[],[false],[false,true],[true]] := by decide
theorem finite_150 : minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [[false,false]] := by decide
theorem finite_151 : minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,true],[true]] := by decide
theorem finite_152 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [] := by decide
theorem finite_153 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [[false,true]] := by decide
theorem finite_154 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[true]] := by decide
theorem finite_155 : minimalVertices [9] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [] := by decide
theorem finite_156 : minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,true],[true]] := by decide
theorem finite_157 : minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [[false,true]] := by decide
theorem finite_158 : minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[true]] := by decide
theorem finite_159 : minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,true],[true]] := by decide
theorem finite_160 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [] := by decide
theorem finite_161 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [[true]] := by decide
theorem finite_162 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [[false],[false,false],[false,true]] := by decide
theorem finite_163 : minimalVertices [9] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [] := by decide
theorem finite_164 : minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,true],[true]] := by decide
theorem finite_165 : minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [[true]] := by decide
theorem finite_166 : minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [[false],[false,false],[false,true]] := by decide
theorem finite_167 : minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,true],[true]] := by decide
theorem finite_168 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [] := by decide
theorem finite_169 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [] := by decide
theorem finite_170 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,true],[true]] := by decide
theorem finite_171 : minimalVertices [9] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [] := by decide
theorem finite_172 : minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,true],[true]] := by decide
theorem finite_173 : minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [] := by decide
theorem finite_174 : minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,true],[true]] := by decide
theorem finite_175 : minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,true],[true]] := by decide
theorem finite_176 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
theorem finite_177 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_178 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
theorem finite_179 : minimalVertices [9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
theorem finite_180 : minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_181 : minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_182 : minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
theorem finite_183 : minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_184 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
theorem finite_185 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false]] := by decide
theorem finite_186 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[true,true,true]] := by decide
theorem finite_187 : minimalVertices [9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
theorem finite_188 : minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_189 : minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false]] := by decide
theorem finite_190 : minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[true,true,true]] := by decide
theorem finite_191 : minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_192 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
theorem finite_193 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,true]] := by decide
theorem finite_194 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[true,true,false]] := by decide
theorem finite_195 : minimalVertices [9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
theorem finite_196 : minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_197 : minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,true]] := by decide
theorem finite_198 : minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[true,true,false]] := by decide
theorem finite_199 : minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_200 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
theorem finite_201 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false]] := by decide
theorem finite_202 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_203 : minimalVertices [9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
theorem finite_204 : minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_205 : minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false]] := by decide
theorem finite_206 : minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_207 : minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_208 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
theorem finite_209 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_210 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[true,false]] := by decide
theorem finite_211 : minimalVertices [9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
theorem finite_212 : minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_213 : minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_214 : minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[true,false]] := by decide
theorem finite_215 : minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_216 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
theorem finite_217 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,true],[true,true,false]] := by decide
theorem finite_218 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[true],[true,false],[true,true],[true,true,true]] := by decide
theorem finite_219 : minimalVertices [9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
theorem finite_220 : minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_221 : minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,true],[true,true,false]] := by decide
theorem finite_222 : minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[true],[true,false],[true,true],[true,true,true]] := by decide
theorem finite_223 : minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_224 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
theorem finite_225 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,true],[true,true,true]] := by decide
theorem finite_226 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[true],[true,false],[true,true],[true,true,false]] := by decide
theorem finite_227 : minimalVertices [9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
theorem finite_228 : minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_229 : minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,true],[true,true,true]] := by decide
theorem finite_230 : minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[true],[true,false],[true,true],[true,true,false]] := by decide
theorem finite_231 : minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_232 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
theorem finite_233 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[false]] := by decide
theorem finite_234 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_235 : minimalVertices [9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
theorem finite_236 : minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_237 : minimalVertices [0, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[false]] := by decide
theorem finite_238 : minimalVertices [1, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_239 : minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_240 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
theorem finite_241 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_242 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[false]] := by decide
theorem finite_243 : minimalVertices [9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
theorem finite_244 : minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_245 : minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_246 : minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[false]] := by decide
theorem finite_247 : minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_248 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
theorem finite_249 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[true],[true,false],[true,true],[true,true,false]] := by decide
theorem finite_250 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,true],[true,true,true]] := by decide
theorem finite_251 : minimalVertices [9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
theorem finite_252 : minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_253 : minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[true],[true,false],[true,true],[true,true,false]] := by decide
theorem finite_254 : minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,true],[true,true,true]] := by decide
theorem finite_255 : minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_256 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
theorem finite_257 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[true],[true,false],[true,true],[true,true,true]] := by decide
theorem finite_258 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,true],[true,true,false]] := by decide
theorem finite_259 : minimalVertices [9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
theorem finite_260 : minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_261 : minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[true],[true,false],[true,true],[true,true,true]] := by decide
theorem finite_262 : minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,true],[true,true,false]] := by decide
theorem finite_263 : minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_264 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
theorem finite_265 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[true,false]] := by decide
theorem finite_266 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_267 : minimalVertices [9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
theorem finite_268 : minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_269 : minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[true,false]] := by decide
theorem finite_270 : minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_271 : minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_272 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
theorem finite_273 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_274 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false]] := by decide
theorem finite_275 : minimalVertices [9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
theorem finite_276 : minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_277 : minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_278 : minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false]] := by decide
theorem finite_279 : minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_280 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
theorem finite_281 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[true,true,false]] := by decide
theorem finite_282 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,true]] := by decide
theorem finite_283 : minimalVertices [9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
theorem finite_284 : minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_285 : minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[true,true,false]] := by decide
theorem finite_286 : minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,true]] := by decide
theorem finite_287 : minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_288 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
theorem finite_289 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[true,true,true]] := by decide
theorem finite_290 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false]] := by decide
theorem finite_291 : minimalVertices [9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
theorem finite_292 : minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_293 : minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[true,true,true]] := by decide
theorem finite_294 : minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false]] := by decide
theorem finite_295 : minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_296 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
theorem finite_297 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
theorem finite_298 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_299 : minimalVertices [9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
theorem finite_300 : minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_301 : minimalVertices [0, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
theorem finite_302 : minimalVertices [1, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_303 : minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] := by decide
theorem finite_304 : minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [] := by decide
theorem finite_305 : minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_306 : minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [] := by decide
theorem finite_307 : minimalVertices [9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [] := by decide
theorem finite_308 : minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_309 : minimalVertices [0, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_310 : minimalVertices [1, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [] := by decide
theorem finite_311 : minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_312 : minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [] := by decide
theorem finite_313 : minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true]] := by decide
theorem finite_314 : minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[true,true]] := by decide
theorem finite_315 : minimalVertices [9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [] := by decide
theorem finite_316 : minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_317 : minimalVertices [0, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true]] := by decide
theorem finite_318 : minimalVertices [1, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[true,true]] := by decide
theorem finite_319 : minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_320 : minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [] := by decide
theorem finite_321 : minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,true]] := by decide
theorem finite_322 : minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[true,false,true]] := by decide
theorem finite_323 : minimalVertices [9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [] := by decide
theorem finite_324 : minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_325 : minimalVertices [0, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,true]] := by decide
theorem finite_326 : minimalVertices [1, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[true,false,true]] := by decide
theorem finite_327 : minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_328 : minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [] := by decide
theorem finite_329 : minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false]] := by decide
theorem finite_330 : minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[true],[true,false],[true,false,true],[true,true]] := by decide
theorem finite_331 : minimalVertices [9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [] := by decide
theorem finite_332 : minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_333 : minimalVertices [0, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false]] := by decide
theorem finite_334 : minimalVertices [1, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[true],[true,false],[true,false,true],[true,true]] := by decide
theorem finite_335 : minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_336 : minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [] := by decide
theorem finite_337 : minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,true],[true,true]] := by decide
theorem finite_338 : minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[true,false,false]] := by decide
theorem finite_339 : minimalVertices [9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [] := by decide
theorem finite_340 : minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_341 : minimalVertices [0, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,true],[true,true]] := by decide
theorem finite_342 : minimalVertices [1, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[true,false,false]] := by decide
theorem finite_343 : minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_344 : minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [] := by decide
theorem finite_345 : minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,true]] := by decide
theorem finite_346 : minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[true],[true,false],[true,false,false],[true,true]] := by decide
theorem finite_347 : minimalVertices [9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [] := by decide
theorem finite_348 : minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_349 : minimalVertices [0, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,true]] := by decide
theorem finite_350 : minimalVertices [1, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[true],[true,false],[true,false,false],[true,true]] := by decide
theorem finite_351 : minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_352 : minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [] := by decide
theorem finite_353 : minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,true]] := by decide
theorem finite_354 : minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[true,false],[true,false,false],[true,false,true]] := by decide
theorem finite_355 : minimalVertices [9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [] := by decide
theorem finite_356 : minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_357 : minimalVertices [0, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,true]] := by decide
theorem finite_358 : minimalVertices [1, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[true,false],[true,false,false],[true,false,true]] := by decide
theorem finite_359 : minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_360 : minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] := by decide
theorem finite_361 : minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[false]] := by decide
theorem finite_362 : minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_363 : minimalVertices [9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] := by decide
theorem finite_364 : minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_365 : minimalVertices [0, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[false]] := by decide
theorem finite_366 : minimalVertices [1, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_367 : minimalVertices [0, 1, 9] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_368 : minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [] := by decide
theorem finite_369 : minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_370 : minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[false]] := by decide
theorem finite_371 : minimalVertices [9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [] := by decide
theorem finite_372 : minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_373 : minimalVertices [0, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_374 : minimalVertices [1, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[false]] := by decide
theorem finite_375 : minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_376 : minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [] := by decide
theorem finite_377 : minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[true,false],[true,false,false],[true,false,true]] := by decide
theorem finite_378 : minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,true]] := by decide
theorem finite_379 : minimalVertices [9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [] := by decide
theorem finite_380 : minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_381 : minimalVertices [0, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[true,false],[true,false,false],[true,false,true]] := by decide
theorem finite_382 : minimalVertices [1, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,true]] := by decide
theorem finite_383 : minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_384 : minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [] := by decide
theorem finite_385 : minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[true],[true,false],[true,false,false],[true,true]] := by decide
theorem finite_386 : minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,true]] := by decide
theorem finite_387 : minimalVertices [9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [] := by decide
theorem finite_388 : minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_389 : minimalVertices [0, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[true],[true,false],[true,false,false],[true,true]] := by decide
theorem finite_390 : minimalVertices [1, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,true]] := by decide
theorem finite_391 : minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_392 : minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [] := by decide
theorem finite_393 : minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[true,false,false]] := by decide
theorem finite_394 : minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,true],[true,true]] := by decide
theorem finite_395 : minimalVertices [9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [] := by decide
theorem finite_396 : minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_397 : minimalVertices [0, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[true,false,false]] := by decide
theorem finite_398 : minimalVertices [1, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,true],[true,true]] := by decide
theorem finite_399 : minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_400 : minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [] := by decide
theorem finite_401 : minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[true],[true,false],[true,false,true],[true,true]] := by decide
theorem finite_402 : minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false]] := by decide
theorem finite_403 : minimalVertices [9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [] := by decide
theorem finite_404 : minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_405 : minimalVertices [0, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[true],[true,false],[true,false,true],[true,true]] := by decide
theorem finite_406 : minimalVertices [1, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false]] := by decide
theorem finite_407 : minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_408 : minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [] := by decide
theorem finite_409 : minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[true,false,true]] := by decide
theorem finite_410 : minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,true]] := by decide
theorem finite_411 : minimalVertices [9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [] := by decide
theorem finite_412 : minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_413 : minimalVertices [0, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[true,false,true]] := by decide
theorem finite_414 : minimalVertices [1, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,true]] := by decide
theorem finite_415 : minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_416 : minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [] := by decide
theorem finite_417 : minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[true,true]] := by decide
theorem finite_418 : minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true]] := by decide
theorem finite_419 : minimalVertices [9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [] := by decide
theorem finite_420 : minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_421 : minimalVertices [0, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[true,true]] := by decide
theorem finite_422 : minimalVertices [1, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true]] := by decide
theorem finite_423 : minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_424 : minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] := by decide
theorem finite_425 : minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] := by decide
theorem finite_426 : minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_427 : minimalVertices [9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] := by decide
theorem finite_428 : minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_429 : minimalVertices [0, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] := by decide
theorem finite_430 : minimalVertices [1, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_431 : minimalVertices [0, 1, 9] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] := by decide
theorem finite_432 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
theorem finite_433 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_434 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
theorem finite_435 : minimalVertices [9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
theorem finite_436 : minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_437 : minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_438 : minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
theorem finite_439 : minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_440 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
theorem finite_441 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false]] := by decide
theorem finite_442 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[true,true]] := by decide
theorem finite_443 : minimalVertices [9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
theorem finite_444 : minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_445 : minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false]] := by decide
theorem finite_446 : minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[true,true]] := by decide
theorem finite_447 : minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_448 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
theorem finite_449 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,true]] := by decide
theorem finite_450 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[true,false]] := by decide
theorem finite_451 : minimalVertices [9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
theorem finite_452 : minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_453 : minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,true]] := by decide
theorem finite_454 : minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[true,false]] := by decide
theorem finite_455 : minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_456 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
theorem finite_457 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[false],[false,false],[false,true]] := by decide
theorem finite_458 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[true],[true,false],[true,true]] := by decide
theorem finite_459 : minimalVertices [9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
theorem finite_460 : minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_461 : minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[false],[false,false],[false,true]] := by decide
theorem finite_462 : minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[true],[true,false],[true,true]] := by decide
theorem finite_463 : minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_464 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
theorem finite_465 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[true],[true,false],[true,true]] := by decide
theorem finite_466 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[false,true]] := by decide
theorem finite_467 : minimalVertices [9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
theorem finite_468 : minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_469 : minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[true],[true,false],[true,true]] := by decide
theorem finite_470 : minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[false,true]] := by decide
theorem finite_471 : minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_472 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
theorem finite_473 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[true],[true,false]] := by decide
theorem finite_474 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,true],[true],[true,true]] := by decide
theorem finite_475 : minimalVertices [9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
theorem finite_476 : minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_477 : minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[true],[true,false]] := by decide
theorem finite_478 : minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,true],[true],[true,true]] := by decide
theorem finite_479 : minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_480 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
theorem finite_481 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[true],[true,true]] := by decide
theorem finite_482 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,true],[true],[true,false]] := by decide
theorem finite_483 : minimalVertices [9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
theorem finite_484 : minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_485 : minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[true],[true,true]] := by decide
theorem finite_486 : minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,true],[true],[true,false]] := by decide
theorem finite_487 : minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_488 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
theorem finite_489 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[false,false]] := by decide
theorem finite_490 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_491 : minimalVertices [9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
theorem finite_492 : minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_493 : minimalVertices [0, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[false,false]] := by decide
theorem finite_494 : minimalVertices [1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_495 : minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_496 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
theorem finite_497 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_498 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[false,false]] := by decide
theorem finite_499 : minimalVertices [9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
theorem finite_500 : minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_501 : minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_502 : minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[false,false]] := by decide
theorem finite_503 : minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_504 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
theorem finite_505 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,true],[true],[true,false]] := by decide
theorem finite_506 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[true],[true,true]] := by decide
theorem finite_507 : minimalVertices [9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
theorem finite_508 : minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_509 : minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,true],[true],[true,false]] := by decide
theorem finite_510 : minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[true],[true,true]] := by decide
theorem finite_511 : minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_512 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
theorem finite_513 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,true],[true],[true,true]] := by decide
theorem finite_514 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[true],[true,false]] := by decide
theorem finite_515 : minimalVertices [9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
theorem finite_516 : minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_517 : minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,true],[true],[true,true]] := by decide
theorem finite_518 : minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[true],[true,false]] := by decide
theorem finite_519 : minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_520 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
theorem finite_521 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[false,true]] := by decide
theorem finite_522 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,false],[true],[true,false],[true,true]] := by decide
theorem finite_523 : minimalVertices [9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
theorem finite_524 : minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_525 : minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[false,true]] := by decide
theorem finite_526 : minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,false],[true],[true,false],[true,true]] := by decide
theorem finite_527 : minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_528 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
theorem finite_529 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[true],[true,false],[true,true]] := by decide
theorem finite_530 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[false],[false,false],[false,true]] := by decide
theorem finite_531 : minimalVertices [9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
theorem finite_532 : minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_533 : minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[true],[true,false],[true,true]] := by decide
theorem finite_534 : minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[false],[false,false],[false,true]] := by decide
theorem finite_535 : minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_536 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
theorem finite_537 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[true,false]] := by decide
theorem finite_538 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,true]] := by decide
theorem finite_539 : minimalVertices [9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
theorem finite_540 : minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_541 : minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[true,false]] := by decide
theorem finite_542 : minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,true]] := by decide
theorem finite_543 : minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_544 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
theorem finite_545 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[true,true]] := by decide
theorem finite_546 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false]] := by decide
theorem finite_547 : minimalVertices [9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
theorem finite_548 : minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_549 : minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[true,true]] := by decide
theorem finite_550 : minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false]] := by decide
theorem finite_551 : minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_552 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
theorem finite_553 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
theorem finite_554 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_555 : minimalVertices [9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
theorem finite_556 : minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_557 : minimalVertices [0, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
theorem finite_558 : minimalVertices [1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_559 : minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] := by decide
theorem finite_560 : minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [] := by decide
theorem finite_561 : minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_562 : minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [] := by decide
theorem finite_563 : minimalVertices [9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [] := by decide
theorem finite_564 : minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_565 : minimalVertices [0, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_566 : minimalVertices [1, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [] := by decide
theorem finite_567 : minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_568 : minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [] := by decide
theorem finite_569 : minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[false],[false,false],[false,true],[false,true,false],[false,true,true]] := by decide
theorem finite_570 : minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[true]] := by decide
theorem finite_571 : minimalVertices [9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [] := by decide
theorem finite_572 : minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_573 : minimalVertices [0, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[false],[false,false],[false,true],[false,true,false],[false,true,true]] := by decide
theorem finite_574 : minimalVertices [1, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[true]] := by decide
theorem finite_575 : minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_576 : minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [] := by decide
theorem finite_577 : minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[true]] := by decide
theorem finite_578 : minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[false,true,true]] := by decide
theorem finite_579 : minimalVertices [9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [] := by decide
theorem finite_580 : minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_581 : minimalVertices [0, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[true]] := by decide
theorem finite_582 : minimalVertices [1, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[false,true,true]] := by decide
theorem finite_583 : minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_584 : minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [] := by decide
theorem finite_585 : minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[false],[false,false],[false,true],[false,true,false]] := by decide
theorem finite_586 : minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[],[false],[false,true],[false,true,true],[true]] := by decide
theorem finite_587 : minimalVertices [9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [] := by decide
theorem finite_588 : minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_589 : minimalVertices [0, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[false],[false,false],[false,true],[false,true,false]] := by decide
theorem finite_590 : minimalVertices [1, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[],[false],[false,true],[false,true,true],[true]] := by decide
theorem finite_591 : minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_592 : minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [] := by decide
theorem finite_593 : minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,true],[true]] := by decide
theorem finite_594 : minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[false,true,false]] := by decide
theorem finite_595 : minimalVertices [9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [] := by decide
theorem finite_596 : minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_597 : minimalVertices [0, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,true],[true]] := by decide
theorem finite_598 : minimalVertices [1, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[false,true,false]] := by decide
theorem finite_599 : minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_600 : minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [] := by decide
theorem finite_601 : minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[false],[false,false],[false,true],[false,true,true]] := by decide
theorem finite_602 : minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[],[false],[false,true],[false,true,false],[true]] := by decide
theorem finite_603 : minimalVertices [9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [] := by decide
theorem finite_604 : minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_605 : minimalVertices [0, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[false],[false,false],[false,true],[false,true,true]] := by decide
theorem finite_606 : minimalVertices [1, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[],[false],[false,true],[false,true,false],[true]] := by decide
theorem finite_607 : minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_608 : minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [] := by decide
theorem finite_609 : minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[true]] := by decide
theorem finite_610 : minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[false,true],[false,true,false],[false,true,true]] := by decide
theorem finite_611 : minimalVertices [9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [] := by decide
theorem finite_612 : minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_613 : minimalVertices [0, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[true]] := by decide
theorem finite_614 : minimalVertices [1, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[false,true],[false,true,false],[false,true,true]] := by decide
theorem finite_615 : minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_616 : minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] := by decide
theorem finite_617 : minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[false,false]] := by decide
theorem finite_618 : minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[],[false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_619 : minimalVertices [9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] := by decide
theorem finite_620 : minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_621 : minimalVertices [0, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[false,false]] := by decide
theorem finite_622 : minimalVertices [1, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[],[false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_623 : minimalVertices [0, 1, 9] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_624 : minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [] := by decide
theorem finite_625 : minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[],[false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_626 : minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[false,false]] := by decide
theorem finite_627 : minimalVertices [9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [] := by decide
theorem finite_628 : minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_629 : minimalVertices [0, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[],[false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_630 : minimalVertices [1, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[false,false]] := by decide
theorem finite_631 : minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_632 : minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [] := by decide
theorem finite_633 : minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[false,true],[false,true,false],[false,true,true]] := by decide
theorem finite_634 : minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[],[false],[false,false],[true]] := by decide
theorem finite_635 : minimalVertices [9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [] := by decide
theorem finite_636 : minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_637 : minimalVertices [0, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[false,true],[false,true,false],[false,true,true]] := by decide
theorem finite_638 : minimalVertices [1, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[],[false],[false,false],[true]] := by decide
theorem finite_639 : minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_640 : minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [] := by decide
theorem finite_641 : minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[],[false],[false,true],[false,true,false],[true]] := by decide
theorem finite_642 : minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[false],[false,false],[false,true],[false,true,true]] := by decide
theorem finite_643 : minimalVertices [9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [] := by decide
theorem finite_644 : minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_645 : minimalVertices [0, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[],[false],[false,true],[false,true,false],[true]] := by decide
theorem finite_646 : minimalVertices [1, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[false],[false,false],[false,true],[false,true,true]] := by decide
theorem finite_647 : minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_648 : minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [] := by decide
theorem finite_649 : minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[false,true,false]] := by decide
theorem finite_650 : minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,true],[true]] := by decide
theorem finite_651 : minimalVertices [9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [] := by decide
theorem finite_652 : minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_653 : minimalVertices [0, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[false,true,false]] := by decide
theorem finite_654 : minimalVertices [1, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,true],[true]] := by decide
theorem finite_655 : minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_656 : minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [] := by decide
theorem finite_657 : minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[],[false],[false,true],[false,true,true],[true]] := by decide
theorem finite_658 : minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[false],[false,false],[false,true],[false,true,false]] := by decide
theorem finite_659 : minimalVertices [9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [] := by decide
theorem finite_660 : minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_661 : minimalVertices [0, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[],[false],[false,true],[false,true,true],[true]] := by decide
theorem finite_662 : minimalVertices [1, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[false],[false,false],[false,true],[false,true,false]] := by decide
theorem finite_663 : minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_664 : minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [] := by decide
theorem finite_665 : minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[false,true,true]] := by decide
theorem finite_666 : minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[true]] := by decide
theorem finite_667 : minimalVertices [9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [] := by decide
theorem finite_668 : minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_669 : minimalVertices [0, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[false,true,true]] := by decide
theorem finite_670 : minimalVertices [1, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[true]] := by decide
theorem finite_671 : minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_672 : minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [] := by decide
theorem finite_673 : minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[true]] := by decide
theorem finite_674 : minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[false],[false,false],[false,true],[false,true,false],[false,true,true]] := by decide
theorem finite_675 : minimalVertices [9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [] := by decide
theorem finite_676 : minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_677 : minimalVertices [0, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[true]] := by decide
theorem finite_678 : minimalVertices [1, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[false],[false,false],[false,true],[false,true,false],[false,true,true]] := by decide
theorem finite_679 : minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_680 : minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] := by decide
theorem finite_681 : minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] := by decide
theorem finite_682 : minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_683 : minimalVertices [9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] := by decide
theorem finite_684 : minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_685 : minimalVertices [0, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] := by decide
theorem finite_686 : minimalVertices [1, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_687 : minimalVertices [0, 1, 9] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] := by decide
theorem finite_688 : minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [] := by decide
theorem finite_689 : minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_690 : minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [] := by decide
theorem finite_691 : minimalVertices [9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [] := by decide
theorem finite_692 : minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_693 : minimalVertices [0, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_694 : minimalVertices [1, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [] := by decide
theorem finite_695 : minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_696 : minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [] := by decide
theorem finite_697 : minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[false],[false,false],[false,false,false],[false,false,true],[false,true]] := by decide
theorem finite_698 : minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[true]] := by decide
theorem finite_699 : minimalVertices [9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [] := by decide
theorem finite_700 : minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_701 : minimalVertices [0, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[false],[false,false],[false,false,false],[false,false,true],[false,true]] := by decide
theorem finite_702 : minimalVertices [1, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[true]] := by decide
theorem finite_703 : minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_704 : minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [] := by decide
theorem finite_705 : minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[true]] := by decide
theorem finite_706 : minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[false,true]] := by decide
theorem finite_707 : minimalVertices [9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [] := by decide
theorem finite_708 : minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_709 : minimalVertices [0, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[true]] := by decide
theorem finite_710 : minimalVertices [1, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[false,true]] := by decide
theorem finite_711 : minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_712 : minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [] := by decide
theorem finite_713 : minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[false,false],[false,false,false],[false,false,true]] := by decide
theorem finite_714 : minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,true],[true]] := by decide
theorem finite_715 : minimalVertices [9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [] := by decide
theorem finite_716 : minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_717 : minimalVertices [0, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[false,false],[false,false,false],[false,false,true]] := by decide
theorem finite_718 : minimalVertices [1, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,true],[true]] := by decide
theorem finite_719 : minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_720 : minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [] := by decide
theorem finite_721 : minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,true],[true]] := by decide
theorem finite_722 : minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[false,false,true]] := by decide
theorem finite_723 : minimalVertices [9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [] := by decide
theorem finite_724 : minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_725 : minimalVertices [0, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,true],[true]] := by decide
theorem finite_726 : minimalVertices [1, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[false,false,true]] := by decide
theorem finite_727 : minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_728 : minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [] := by decide
theorem finite_729 : minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[false],[false,false],[false,false,false],[false,true]] := by decide
theorem finite_730 : minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,true],[true]] := by decide
theorem finite_731 : minimalVertices [9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [] := by decide
theorem finite_732 : minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_733 : minimalVertices [0, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[false],[false,false],[false,false,false],[false,true]] := by decide
theorem finite_734 : minimalVertices [1, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,true],[true]] := by decide
theorem finite_735 : minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_736 : minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [] := by decide
theorem finite_737 : minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[true]] := by decide
theorem finite_738 : minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[false],[false,false],[false,false,true],[false,true]] := by decide
theorem finite_739 : minimalVertices [9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [] := by decide
theorem finite_740 : minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_741 : minimalVertices [0, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[true]] := by decide
theorem finite_742 : minimalVertices [1, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[false],[false,false],[false,false,true],[false,true]] := by decide
theorem finite_743 : minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_744 : minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] := by decide
theorem finite_745 : minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[false,false,false]] := by decide
theorem finite_746 : minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_747 : minimalVertices [9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] := by decide
theorem finite_748 : minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_749 : minimalVertices [0, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[false,false,false]] := by decide
theorem finite_750 : minimalVertices [1, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_751 : minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_752 : minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [] := by decide
theorem finite_753 : minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_754 : minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[false,false,false]] := by decide
theorem finite_755 : minimalVertices [9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [] := by decide
theorem finite_756 : minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_757 : minimalVertices [0, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_758 : minimalVertices [1, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[false,false,false]] := by decide
theorem finite_759 : minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_760 : minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [] := by decide
theorem finite_761 : minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[false],[false,false],[false,false,true],[false,true]] := by decide
theorem finite_762 : minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[true]] := by decide
theorem finite_763 : minimalVertices [9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [] := by decide
theorem finite_764 : minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_765 : minimalVertices [0, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[false],[false,false],[false,false,true],[false,true]] := by decide
theorem finite_766 : minimalVertices [1, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[true]] := by decide
theorem finite_767 : minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_768 : minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [] := by decide
theorem finite_769 : minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,true],[true]] := by decide
theorem finite_770 : minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[false],[false,false],[false,false,false],[false,true]] := by decide
theorem finite_771 : minimalVertices [9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [] := by decide
theorem finite_772 : minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_773 : minimalVertices [0, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,true],[true]] := by decide
theorem finite_774 : minimalVertices [1, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[false],[false,false],[false,false,false],[false,true]] := by decide
theorem finite_775 : minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_776 : minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [] := by decide
theorem finite_777 : minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[false,false,true]] := by decide
theorem finite_778 : minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,true],[true]] := by decide
theorem finite_779 : minimalVertices [9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [] := by decide
theorem finite_780 : minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_781 : minimalVertices [0, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[false,false,true]] := by decide
theorem finite_782 : minimalVertices [1, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,true],[true]] := by decide
theorem finite_783 : minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_784 : minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [] := by decide
theorem finite_785 : minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,true],[true]] := by decide
theorem finite_786 : minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[false,false],[false,false,false],[false,false,true]] := by decide
theorem finite_787 : minimalVertices [9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [] := by decide
theorem finite_788 : minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_789 : minimalVertices [0, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,true],[true]] := by decide
theorem finite_790 : minimalVertices [1, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[false,false],[false,false,false],[false,false,true]] := by decide
theorem finite_791 : minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_792 : minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [] := by decide
theorem finite_793 : minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[false,true]] := by decide
theorem finite_794 : minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[true]] := by decide
theorem finite_795 : minimalVertices [9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [] := by decide
theorem finite_796 : minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_797 : minimalVertices [0, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[false,true]] := by decide
theorem finite_798 : minimalVertices [1, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[true]] := by decide
theorem finite_799 : minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_800 : minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [] := by decide
theorem finite_801 : minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[true]] := by decide
theorem finite_802 : minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[false],[false,false],[false,false,false],[false,false,true],[false,true]] := by decide
theorem finite_803 : minimalVertices [9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [] := by decide
theorem finite_804 : minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_805 : minimalVertices [0, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[true]] := by decide
theorem finite_806 : minimalVertices [1, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[false],[false,false],[false,false,false],[false,false,true],[false,true]] := by decide
theorem finite_807 : minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_808 : minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] := by decide
theorem finite_809 : minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] := by decide
theorem finite_810 : minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_811 : minimalVertices [9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] := by decide
theorem finite_812 : minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_813 : minimalVertices [0, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] := by decide
theorem finite_814 : minimalVertices [1, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
theorem finite_815 : minimalVertices [0, 1, 9] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] := by decide
end FreshExecutableReview
