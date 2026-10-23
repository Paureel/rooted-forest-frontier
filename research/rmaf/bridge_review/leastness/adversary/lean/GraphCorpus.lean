import RMAF
namespace LeastnessAdversary
set_option maxRecDepth 10000
theorem GraphCorpus_0 : RMAF.minimalVertices [] (.leaf 0) = [] := by decide
#print axioms GraphCorpus_0
theorem GraphCorpus_1 : RMAF.minimalVertices [0] (.leaf 0) = [[]] := by decide
#print axioms GraphCorpus_1
theorem GraphCorpus_2 : RMAF.minimalVertices [1] (.leaf 0) = [] := by decide
#print axioms GraphCorpus_2
theorem GraphCorpus_3 : RMAF.minimalVertices [0, 1] (.leaf 0) = [[]] := by decide
#print axioms GraphCorpus_3
theorem GraphCorpus_4 : RMAF.minimalVertices [2] (.leaf 0) = [] := by decide
#print axioms GraphCorpus_4
theorem GraphCorpus_5 : RMAF.minimalVertices [0, 0] (.leaf 0) = [[]] := by decide
#print axioms GraphCorpus_5
theorem GraphCorpus_6 : RMAF.minimalVertices [1, 1] (.leaf 0) = [] := by decide
#print axioms GraphCorpus_6
theorem GraphCorpus_7 : RMAF.minimalVertices [0, 1, 0, 1] (.leaf 0) = [[]] := by decide
#print axioms GraphCorpus_7
theorem GraphCorpus_8 : RMAF.minimalVertices [] (.leaf 1) = [] := by decide
#print axioms GraphCorpus_8
theorem GraphCorpus_9 : RMAF.minimalVertices [0] (.leaf 1) = [] := by decide
#print axioms GraphCorpus_9
theorem GraphCorpus_10 : RMAF.minimalVertices [1] (.leaf 1) = [[]] := by decide
#print axioms GraphCorpus_10
theorem GraphCorpus_11 : RMAF.minimalVertices [0, 1] (.leaf 1) = [[]] := by decide
#print axioms GraphCorpus_11
theorem GraphCorpus_12 : RMAF.minimalVertices [2] (.leaf 1) = [] := by decide
#print axioms GraphCorpus_12
theorem GraphCorpus_13 : RMAF.minimalVertices [0, 0] (.leaf 1) = [] := by decide
#print axioms GraphCorpus_13
theorem GraphCorpus_14 : RMAF.minimalVertices [1, 1] (.leaf 1) = [[]] := by decide
#print axioms GraphCorpus_14
theorem GraphCorpus_15 : RMAF.minimalVertices [0, 1, 0, 1] (.leaf 1) = [[]] := by decide
#print axioms GraphCorpus_15
theorem GraphCorpus_16 : RMAF.minimalVertices [] (.node (.leaf 0) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_16
theorem GraphCorpus_17 : RMAF.minimalVertices [0] (.node (.leaf 0) (.leaf 0)) = [[], [false], [true]] := by decide
#print axioms GraphCorpus_17
theorem GraphCorpus_18 : RMAF.minimalVertices [1] (.node (.leaf 0) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_18
theorem GraphCorpus_19 : RMAF.minimalVertices [0, 1] (.node (.leaf 0) (.leaf 0)) = [[], [false], [true]] := by decide
#print axioms GraphCorpus_19
theorem GraphCorpus_20 : RMAF.minimalVertices [2] (.node (.leaf 0) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_20
theorem GraphCorpus_21 : RMAF.minimalVertices [0, 0] (.node (.leaf 0) (.leaf 0)) = [[], [false], [true]] := by decide
#print axioms GraphCorpus_21
theorem GraphCorpus_22 : RMAF.minimalVertices [1, 1] (.node (.leaf 0) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_22
theorem GraphCorpus_23 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 0) (.leaf 0)) = [[], [false], [true]] := by decide
#print axioms GraphCorpus_23
theorem GraphCorpus_24 : RMAF.minimalVertices [] (.node (.leaf 0) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_24
theorem GraphCorpus_25 : RMAF.minimalVertices [0] (.node (.leaf 0) (.leaf 1)) = [[false]] := by decide
#print axioms GraphCorpus_25
theorem GraphCorpus_26 : RMAF.minimalVertices [1] (.node (.leaf 0) (.leaf 1)) = [[true]] := by decide
#print axioms GraphCorpus_26
theorem GraphCorpus_27 : RMAF.minimalVertices [0, 1] (.node (.leaf 0) (.leaf 1)) = [[], [false], [true]] := by decide
#print axioms GraphCorpus_27
theorem GraphCorpus_28 : RMAF.minimalVertices [2] (.node (.leaf 0) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_28
theorem GraphCorpus_29 : RMAF.minimalVertices [0, 0] (.node (.leaf 0) (.leaf 1)) = [[false]] := by decide
#print axioms GraphCorpus_29
theorem GraphCorpus_30 : RMAF.minimalVertices [1, 1] (.node (.leaf 0) (.leaf 1)) = [[true]] := by decide
#print axioms GraphCorpus_30
theorem GraphCorpus_31 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 0) (.leaf 1)) = [[], [false], [true]] := by decide
#print axioms GraphCorpus_31
theorem GraphCorpus_32 : RMAF.minimalVertices [] (.node (.leaf 1) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_32
theorem GraphCorpus_33 : RMAF.minimalVertices [0] (.node (.leaf 1) (.leaf 0)) = [[true]] := by decide
#print axioms GraphCorpus_33
theorem GraphCorpus_34 : RMAF.minimalVertices [1] (.node (.leaf 1) (.leaf 0)) = [[false]] := by decide
#print axioms GraphCorpus_34
theorem GraphCorpus_35 : RMAF.minimalVertices [0, 1] (.node (.leaf 1) (.leaf 0)) = [[], [false], [true]] := by decide
#print axioms GraphCorpus_35
theorem GraphCorpus_36 : RMAF.minimalVertices [2] (.node (.leaf 1) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_36
theorem GraphCorpus_37 : RMAF.minimalVertices [0, 0] (.node (.leaf 1) (.leaf 0)) = [[true]] := by decide
#print axioms GraphCorpus_37
theorem GraphCorpus_38 : RMAF.minimalVertices [1, 1] (.node (.leaf 1) (.leaf 0)) = [[false]] := by decide
#print axioms GraphCorpus_38
theorem GraphCorpus_39 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 1) (.leaf 0)) = [[], [false], [true]] := by decide
#print axioms GraphCorpus_39
theorem GraphCorpus_40 : RMAF.minimalVertices [] (.node (.leaf 1) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_40
theorem GraphCorpus_41 : RMAF.minimalVertices [0] (.node (.leaf 1) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_41
theorem GraphCorpus_42 : RMAF.minimalVertices [1] (.node (.leaf 1) (.leaf 1)) = [[], [false], [true]] := by decide
#print axioms GraphCorpus_42
theorem GraphCorpus_43 : RMAF.minimalVertices [0, 1] (.node (.leaf 1) (.leaf 1)) = [[], [false], [true]] := by decide
#print axioms GraphCorpus_43
theorem GraphCorpus_44 : RMAF.minimalVertices [2] (.node (.leaf 1) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_44
theorem GraphCorpus_45 : RMAF.minimalVertices [0, 0] (.node (.leaf 1) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_45
theorem GraphCorpus_46 : RMAF.minimalVertices [1, 1] (.node (.leaf 1) (.leaf 1)) = [[], [false], [true]] := by decide
#print axioms GraphCorpus_46
theorem GraphCorpus_47 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 1) (.leaf 1)) = [[], [false], [true]] := by decide
#print axioms GraphCorpus_47
theorem GraphCorpus_48 : RMAF.minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_48
theorem GraphCorpus_49 : RMAF.minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [[], [false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_49
theorem GraphCorpus_50 : RMAF.minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_50
theorem GraphCorpus_51 : RMAF.minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [[], [false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_51
theorem GraphCorpus_52 : RMAF.minimalVertices [2] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_52
theorem GraphCorpus_53 : RMAF.minimalVertices [0, 0] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [[], [false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_53
theorem GraphCorpus_54 : RMAF.minimalVertices [1, 1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_54
theorem GraphCorpus_55 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [[], [false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_55
theorem GraphCorpus_56 : RMAF.minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_56
theorem GraphCorpus_57 : RMAF.minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [[], [false], [true], [true, false]] := by decide
#print axioms GraphCorpus_57
theorem GraphCorpus_58 : RMAF.minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [[true, true]] := by decide
#print axioms GraphCorpus_58
theorem GraphCorpus_59 : RMAF.minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [[], [false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_59
theorem GraphCorpus_60 : RMAF.minimalVertices [2] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_60
theorem GraphCorpus_61 : RMAF.minimalVertices [0, 0] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [[], [false], [true], [true, false]] := by decide
#print axioms GraphCorpus_61
theorem GraphCorpus_62 : RMAF.minimalVertices [1, 1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [[true, true]] := by decide
#print axioms GraphCorpus_62
theorem GraphCorpus_63 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [[], [false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_63
theorem GraphCorpus_64 : RMAF.minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_64
theorem GraphCorpus_65 : RMAF.minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [[], [false], [true], [true, true]] := by decide
#print axioms GraphCorpus_65
theorem GraphCorpus_66 : RMAF.minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [[true, false]] := by decide
#print axioms GraphCorpus_66
theorem GraphCorpus_67 : RMAF.minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [[], [false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_67
theorem GraphCorpus_68 : RMAF.minimalVertices [2] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_68
theorem GraphCorpus_69 : RMAF.minimalVertices [0, 0] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [[], [false], [true], [true, true]] := by decide
#print axioms GraphCorpus_69
theorem GraphCorpus_70 : RMAF.minimalVertices [1, 1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [[true, false]] := by decide
#print axioms GraphCorpus_70
theorem GraphCorpus_71 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [[], [false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_71
theorem GraphCorpus_72 : RMAF.minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_72
theorem GraphCorpus_73 : RMAF.minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [[false]] := by decide
#print axioms GraphCorpus_73
theorem GraphCorpus_74 : RMAF.minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [[true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_74
theorem GraphCorpus_75 : RMAF.minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [[], [false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_75
theorem GraphCorpus_76 : RMAF.minimalVertices [2] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_76
theorem GraphCorpus_77 : RMAF.minimalVertices [0, 0] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [[false]] := by decide
#print axioms GraphCorpus_77
theorem GraphCorpus_78 : RMAF.minimalVertices [1, 1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [[true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_78
theorem GraphCorpus_79 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [[], [false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_79
theorem GraphCorpus_80 : RMAF.minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_80
theorem GraphCorpus_81 : RMAF.minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [[true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_81
theorem GraphCorpus_82 : RMAF.minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [[false]] := by decide
#print axioms GraphCorpus_82
theorem GraphCorpus_83 : RMAF.minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [[], [false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_83
theorem GraphCorpus_84 : RMAF.minimalVertices [2] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_84
theorem GraphCorpus_85 : RMAF.minimalVertices [0, 0] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [[true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_85
theorem GraphCorpus_86 : RMAF.minimalVertices [1, 1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [[false]] := by decide
#print axioms GraphCorpus_86
theorem GraphCorpus_87 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [[], [false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_87
theorem GraphCorpus_88 : RMAF.minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_88
theorem GraphCorpus_89 : RMAF.minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [[true, false]] := by decide
#print axioms GraphCorpus_89
theorem GraphCorpus_90 : RMAF.minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [[], [false], [true], [true, true]] := by decide
#print axioms GraphCorpus_90
theorem GraphCorpus_91 : RMAF.minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [[], [false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_91
theorem GraphCorpus_92 : RMAF.minimalVertices [2] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_92
theorem GraphCorpus_93 : RMAF.minimalVertices [0, 0] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [[true, false]] := by decide
#print axioms GraphCorpus_93
theorem GraphCorpus_94 : RMAF.minimalVertices [1, 1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [[], [false], [true], [true, true]] := by decide
#print axioms GraphCorpus_94
theorem GraphCorpus_95 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [[], [false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_95
theorem GraphCorpus_96 : RMAF.minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_96
theorem GraphCorpus_97 : RMAF.minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [[true, true]] := by decide
#print axioms GraphCorpus_97
theorem GraphCorpus_98 : RMAF.minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [[], [false], [true], [true, false]] := by decide
#print axioms GraphCorpus_98
theorem GraphCorpus_99 : RMAF.minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [[], [false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_99
theorem GraphCorpus_100 : RMAF.minimalVertices [2] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_100
theorem GraphCorpus_101 : RMAF.minimalVertices [0, 0] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [[true, true]] := by decide
#print axioms GraphCorpus_101
theorem GraphCorpus_102 : RMAF.minimalVertices [1, 1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [[], [false], [true], [true, false]] := by decide
#print axioms GraphCorpus_102
theorem GraphCorpus_103 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [[], [false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_103
theorem GraphCorpus_104 : RMAF.minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_104
theorem GraphCorpus_105 : RMAF.minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_105
theorem GraphCorpus_106 : RMAF.minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [[], [false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_106
theorem GraphCorpus_107 : RMAF.minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [[], [false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_107
theorem GraphCorpus_108 : RMAF.minimalVertices [2] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_108
theorem GraphCorpus_109 : RMAF.minimalVertices [0, 0] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_109
theorem GraphCorpus_110 : RMAF.minimalVertices [1, 1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [[], [false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_110
theorem GraphCorpus_111 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [[], [false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_111
theorem GraphCorpus_112 : RMAF.minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_112
theorem GraphCorpus_113 : RMAF.minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [[], [false], [false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_113
theorem GraphCorpus_114 : RMAF.minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_114
theorem GraphCorpus_115 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [[], [false], [false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_115
theorem GraphCorpus_116 : RMAF.minimalVertices [2] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_116
theorem GraphCorpus_117 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [[], [false], [false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_117
theorem GraphCorpus_118 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_118
theorem GraphCorpus_119 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [[], [false], [false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_119
theorem GraphCorpus_120 : RMAF.minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_120
theorem GraphCorpus_121 : RMAF.minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [[false], [false, false], [false, true]] := by decide
#print axioms GraphCorpus_121
theorem GraphCorpus_122 : RMAF.minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [[true]] := by decide
#print axioms GraphCorpus_122
theorem GraphCorpus_123 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [[], [false], [false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_123
theorem GraphCorpus_124 : RMAF.minimalVertices [2] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_124
theorem GraphCorpus_125 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [[false], [false, false], [false, true]] := by decide
#print axioms GraphCorpus_125
theorem GraphCorpus_126 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [[true]] := by decide
#print axioms GraphCorpus_126
theorem GraphCorpus_127 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [[], [false], [false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_127
theorem GraphCorpus_128 : RMAF.minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_128
theorem GraphCorpus_129 : RMAF.minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [[], [false], [false, false], [true]] := by decide
#print axioms GraphCorpus_129
theorem GraphCorpus_130 : RMAF.minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [[false, true]] := by decide
#print axioms GraphCorpus_130
theorem GraphCorpus_131 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [[], [false], [false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_131
theorem GraphCorpus_132 : RMAF.minimalVertices [2] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_132
theorem GraphCorpus_133 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [[], [false], [false, false], [true]] := by decide
#print axioms GraphCorpus_133
theorem GraphCorpus_134 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [[false, true]] := by decide
#print axioms GraphCorpus_134
theorem GraphCorpus_135 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [[], [false], [false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_135
theorem GraphCorpus_136 : RMAF.minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_136
theorem GraphCorpus_137 : RMAF.minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [[false, false]] := by decide
#print axioms GraphCorpus_137
theorem GraphCorpus_138 : RMAF.minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [[], [false], [false, true], [true]] := by decide
#print axioms GraphCorpus_138
theorem GraphCorpus_139 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [[], [false], [false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_139
theorem GraphCorpus_140 : RMAF.minimalVertices [2] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_140
theorem GraphCorpus_141 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [[false, false]] := by decide
#print axioms GraphCorpus_141
theorem GraphCorpus_142 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [[], [false], [false, true], [true]] := by decide
#print axioms GraphCorpus_142
theorem GraphCorpus_143 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [[], [false], [false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_143
theorem GraphCorpus_144 : RMAF.minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_144
theorem GraphCorpus_145 : RMAF.minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [[], [false], [false, true], [true]] := by decide
#print axioms GraphCorpus_145
theorem GraphCorpus_146 : RMAF.minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [[false, false]] := by decide
#print axioms GraphCorpus_146
theorem GraphCorpus_147 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [[], [false], [false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_147
theorem GraphCorpus_148 : RMAF.minimalVertices [2] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_148
theorem GraphCorpus_149 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [[], [false], [false, true], [true]] := by decide
#print axioms GraphCorpus_149
theorem GraphCorpus_150 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [[false, false]] := by decide
#print axioms GraphCorpus_150
theorem GraphCorpus_151 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [[], [false], [false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_151
theorem GraphCorpus_152 : RMAF.minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_152
theorem GraphCorpus_153 : RMAF.minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [[false, true]] := by decide
#print axioms GraphCorpus_153
theorem GraphCorpus_154 : RMAF.minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [[], [false], [false, false], [true]] := by decide
#print axioms GraphCorpus_154
theorem GraphCorpus_155 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [[], [false], [false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_155
theorem GraphCorpus_156 : RMAF.minimalVertices [2] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_156
theorem GraphCorpus_157 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [[false, true]] := by decide
#print axioms GraphCorpus_157
theorem GraphCorpus_158 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [[], [false], [false, false], [true]] := by decide
#print axioms GraphCorpus_158
theorem GraphCorpus_159 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [[], [false], [false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_159
theorem GraphCorpus_160 : RMAF.minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_160
theorem GraphCorpus_161 : RMAF.minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [[true]] := by decide
#print axioms GraphCorpus_161
theorem GraphCorpus_162 : RMAF.minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [[false], [false, false], [false, true]] := by decide
#print axioms GraphCorpus_162
theorem GraphCorpus_163 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [[], [false], [false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_163
theorem GraphCorpus_164 : RMAF.minimalVertices [2] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_164
theorem GraphCorpus_165 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [[true]] := by decide
#print axioms GraphCorpus_165
theorem GraphCorpus_166 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [[false], [false, false], [false, true]] := by decide
#print axioms GraphCorpus_166
theorem GraphCorpus_167 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [[], [false], [false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_167
theorem GraphCorpus_168 : RMAF.minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_168
theorem GraphCorpus_169 : RMAF.minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_169
theorem GraphCorpus_170 : RMAF.minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [[], [false], [false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_170
theorem GraphCorpus_171 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [[], [false], [false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_171
theorem GraphCorpus_172 : RMAF.minimalVertices [2] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_172
theorem GraphCorpus_173 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_173
theorem GraphCorpus_174 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [[], [false], [false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_174
theorem GraphCorpus_175 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [[], [false], [false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_175
theorem GraphCorpus_176 : RMAF.minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
#print axioms GraphCorpus_176
theorem GraphCorpus_177 : RMAF.minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_177
theorem GraphCorpus_178 : RMAF.minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
#print axioms GraphCorpus_178
theorem GraphCorpus_179 : RMAF.minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_179
theorem GraphCorpus_180 : RMAF.minimalVertices [2] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
#print axioms GraphCorpus_180
theorem GraphCorpus_181 : RMAF.minimalVertices [0, 0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_181
theorem GraphCorpus_182 : RMAF.minimalVertices [1, 1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
#print axioms GraphCorpus_182
theorem GraphCorpus_183 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_183
theorem GraphCorpus_184 : RMAF.minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
#print axioms GraphCorpus_184
theorem GraphCorpus_185 : RMAF.minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[], [false], [true], [true, false], [true, true], [true, true, false]] := by decide
#print axioms GraphCorpus_185
theorem GraphCorpus_186 : RMAF.minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[true, true, true]] := by decide
#print axioms GraphCorpus_186
theorem GraphCorpus_187 : RMAF.minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_187
theorem GraphCorpus_188 : RMAF.minimalVertices [2] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
#print axioms GraphCorpus_188
theorem GraphCorpus_189 : RMAF.minimalVertices [0, 0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[], [false], [true], [true, false], [true, true], [true, true, false]] := by decide
#print axioms GraphCorpus_189
theorem GraphCorpus_190 : RMAF.minimalVertices [1, 1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[true, true, true]] := by decide
#print axioms GraphCorpus_190
theorem GraphCorpus_191 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_191
theorem GraphCorpus_192 : RMAF.minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
#print axioms GraphCorpus_192
theorem GraphCorpus_193 : RMAF.minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[], [false], [true], [true, false], [true, true], [true, true, true]] := by decide
#print axioms GraphCorpus_193
theorem GraphCorpus_194 : RMAF.minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[true, true, false]] := by decide
#print axioms GraphCorpus_194
theorem GraphCorpus_195 : RMAF.minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_195
theorem GraphCorpus_196 : RMAF.minimalVertices [2] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
#print axioms GraphCorpus_196
theorem GraphCorpus_197 : RMAF.minimalVertices [0, 0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[], [false], [true], [true, false], [true, true], [true, true, true]] := by decide
#print axioms GraphCorpus_197
theorem GraphCorpus_198 : RMAF.minimalVertices [1, 1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[true, true, false]] := by decide
#print axioms GraphCorpus_198
theorem GraphCorpus_199 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_199
theorem GraphCorpus_200 : RMAF.minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
#print axioms GraphCorpus_200
theorem GraphCorpus_201 : RMAF.minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[], [false], [true], [true, false]] := by decide
#print axioms GraphCorpus_201
theorem GraphCorpus_202 : RMAF.minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_202
theorem GraphCorpus_203 : RMAF.minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_203
theorem GraphCorpus_204 : RMAF.minimalVertices [2] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
#print axioms GraphCorpus_204
theorem GraphCorpus_205 : RMAF.minimalVertices [0, 0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[], [false], [true], [true, false]] := by decide
#print axioms GraphCorpus_205
theorem GraphCorpus_206 : RMAF.minimalVertices [1, 1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_206
theorem GraphCorpus_207 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_207
theorem GraphCorpus_208 : RMAF.minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
#print axioms GraphCorpus_208
theorem GraphCorpus_209 : RMAF.minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[], [false], [true], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_209
theorem GraphCorpus_210 : RMAF.minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[true, false]] := by decide
#print axioms GraphCorpus_210
theorem GraphCorpus_211 : RMAF.minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_211
theorem GraphCorpus_212 : RMAF.minimalVertices [2] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
#print axioms GraphCorpus_212
theorem GraphCorpus_213 : RMAF.minimalVertices [0, 0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[], [false], [true], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_213
theorem GraphCorpus_214 : RMAF.minimalVertices [1, 1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[true, false]] := by decide
#print axioms GraphCorpus_214
theorem GraphCorpus_215 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_215
theorem GraphCorpus_216 : RMAF.minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
#print axioms GraphCorpus_216
theorem GraphCorpus_217 : RMAF.minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[], [false], [true], [true, true], [true, true, false]] := by decide
#print axioms GraphCorpus_217
theorem GraphCorpus_218 : RMAF.minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[true], [true, false], [true, true], [true, true, true]] := by decide
#print axioms GraphCorpus_218
theorem GraphCorpus_219 : RMAF.minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_219
theorem GraphCorpus_220 : RMAF.minimalVertices [2] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
#print axioms GraphCorpus_220
theorem GraphCorpus_221 : RMAF.minimalVertices [0, 0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[], [false], [true], [true, true], [true, true, false]] := by decide
#print axioms GraphCorpus_221
theorem GraphCorpus_222 : RMAF.minimalVertices [1, 1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[true], [true, false], [true, true], [true, true, true]] := by decide
#print axioms GraphCorpus_222
theorem GraphCorpus_223 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_223
theorem GraphCorpus_224 : RMAF.minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
#print axioms GraphCorpus_224
theorem GraphCorpus_225 : RMAF.minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[], [false], [true], [true, true], [true, true, true]] := by decide
#print axioms GraphCorpus_225
theorem GraphCorpus_226 : RMAF.minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[true], [true, false], [true, true], [true, true, false]] := by decide
#print axioms GraphCorpus_226
theorem GraphCorpus_227 : RMAF.minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_227
theorem GraphCorpus_228 : RMAF.minimalVertices [2] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
#print axioms GraphCorpus_228
theorem GraphCorpus_229 : RMAF.minimalVertices [0, 0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[], [false], [true], [true, true], [true, true, true]] := by decide
#print axioms GraphCorpus_229
theorem GraphCorpus_230 : RMAF.minimalVertices [1, 1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[true], [true, false], [true, true], [true, true, false]] := by decide
#print axioms GraphCorpus_230
theorem GraphCorpus_231 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_231
theorem GraphCorpus_232 : RMAF.minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
#print axioms GraphCorpus_232
theorem GraphCorpus_233 : RMAF.minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[false]] := by decide
#print axioms GraphCorpus_233
theorem GraphCorpus_234 : RMAF.minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_234
theorem GraphCorpus_235 : RMAF.minimalVertices [0, 1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_235
theorem GraphCorpus_236 : RMAF.minimalVertices [2] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
#print axioms GraphCorpus_236
theorem GraphCorpus_237 : RMAF.minimalVertices [0, 0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[false]] := by decide
#print axioms GraphCorpus_237
theorem GraphCorpus_238 : RMAF.minimalVertices [1, 1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_238
theorem GraphCorpus_239 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_239
theorem GraphCorpus_240 : RMAF.minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
#print axioms GraphCorpus_240
theorem GraphCorpus_241 : RMAF.minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_241
theorem GraphCorpus_242 : RMAF.minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[false]] := by decide
#print axioms GraphCorpus_242
theorem GraphCorpus_243 : RMAF.minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_243
theorem GraphCorpus_244 : RMAF.minimalVertices [2] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
#print axioms GraphCorpus_244
theorem GraphCorpus_245 : RMAF.minimalVertices [0, 0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_245
theorem GraphCorpus_246 : RMAF.minimalVertices [1, 1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[false]] := by decide
#print axioms GraphCorpus_246
theorem GraphCorpus_247 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_247
theorem GraphCorpus_248 : RMAF.minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
#print axioms GraphCorpus_248
theorem GraphCorpus_249 : RMAF.minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[true], [true, false], [true, true], [true, true, false]] := by decide
#print axioms GraphCorpus_249
theorem GraphCorpus_250 : RMAF.minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[], [false], [true], [true, true], [true, true, true]] := by decide
#print axioms GraphCorpus_250
theorem GraphCorpus_251 : RMAF.minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_251
theorem GraphCorpus_252 : RMAF.minimalVertices [2] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
#print axioms GraphCorpus_252
theorem GraphCorpus_253 : RMAF.minimalVertices [0, 0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[true], [true, false], [true, true], [true, true, false]] := by decide
#print axioms GraphCorpus_253
theorem GraphCorpus_254 : RMAF.minimalVertices [1, 1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[], [false], [true], [true, true], [true, true, true]] := by decide
#print axioms GraphCorpus_254
theorem GraphCorpus_255 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_255
theorem GraphCorpus_256 : RMAF.minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
#print axioms GraphCorpus_256
theorem GraphCorpus_257 : RMAF.minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[true], [true, false], [true, true], [true, true, true]] := by decide
#print axioms GraphCorpus_257
theorem GraphCorpus_258 : RMAF.minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[], [false], [true], [true, true], [true, true, false]] := by decide
#print axioms GraphCorpus_258
theorem GraphCorpus_259 : RMAF.minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_259
theorem GraphCorpus_260 : RMAF.minimalVertices [2] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
#print axioms GraphCorpus_260
theorem GraphCorpus_261 : RMAF.minimalVertices [0, 0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[true], [true, false], [true, true], [true, true, true]] := by decide
#print axioms GraphCorpus_261
theorem GraphCorpus_262 : RMAF.minimalVertices [1, 1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[], [false], [true], [true, true], [true, true, false]] := by decide
#print axioms GraphCorpus_262
theorem GraphCorpus_263 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_263
theorem GraphCorpus_264 : RMAF.minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
#print axioms GraphCorpus_264
theorem GraphCorpus_265 : RMAF.minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[true, false]] := by decide
#print axioms GraphCorpus_265
theorem GraphCorpus_266 : RMAF.minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[], [false], [true], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_266
theorem GraphCorpus_267 : RMAF.minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_267
theorem GraphCorpus_268 : RMAF.minimalVertices [2] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
#print axioms GraphCorpus_268
theorem GraphCorpus_269 : RMAF.minimalVertices [0, 0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[true, false]] := by decide
#print axioms GraphCorpus_269
theorem GraphCorpus_270 : RMAF.minimalVertices [1, 1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[], [false], [true], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_270
theorem GraphCorpus_271 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_271
theorem GraphCorpus_272 : RMAF.minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
#print axioms GraphCorpus_272
theorem GraphCorpus_273 : RMAF.minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_273
theorem GraphCorpus_274 : RMAF.minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[], [false], [true], [true, false]] := by decide
#print axioms GraphCorpus_274
theorem GraphCorpus_275 : RMAF.minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_275
theorem GraphCorpus_276 : RMAF.minimalVertices [2] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
#print axioms GraphCorpus_276
theorem GraphCorpus_277 : RMAF.minimalVertices [0, 0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_277
theorem GraphCorpus_278 : RMAF.minimalVertices [1, 1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[], [false], [true], [true, false]] := by decide
#print axioms GraphCorpus_278
theorem GraphCorpus_279 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_279
theorem GraphCorpus_280 : RMAF.minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
#print axioms GraphCorpus_280
theorem GraphCorpus_281 : RMAF.minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[true, true, false]] := by decide
#print axioms GraphCorpus_281
theorem GraphCorpus_282 : RMAF.minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[], [false], [true], [true, false], [true, true], [true, true, true]] := by decide
#print axioms GraphCorpus_282
theorem GraphCorpus_283 : RMAF.minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_283
theorem GraphCorpus_284 : RMAF.minimalVertices [2] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
#print axioms GraphCorpus_284
theorem GraphCorpus_285 : RMAF.minimalVertices [0, 0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[true, true, false]] := by decide
#print axioms GraphCorpus_285
theorem GraphCorpus_286 : RMAF.minimalVertices [1, 1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[], [false], [true], [true, false], [true, true], [true, true, true]] := by decide
#print axioms GraphCorpus_286
theorem GraphCorpus_287 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_287
theorem GraphCorpus_288 : RMAF.minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
#print axioms GraphCorpus_288
theorem GraphCorpus_289 : RMAF.minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[true, true, true]] := by decide
#print axioms GraphCorpus_289
theorem GraphCorpus_290 : RMAF.minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[], [false], [true], [true, false], [true, true], [true, true, false]] := by decide
#print axioms GraphCorpus_290
theorem GraphCorpus_291 : RMAF.minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_291
theorem GraphCorpus_292 : RMAF.minimalVertices [2] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
#print axioms GraphCorpus_292
theorem GraphCorpus_293 : RMAF.minimalVertices [0, 0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[true, true, true]] := by decide
#print axioms GraphCorpus_293
theorem GraphCorpus_294 : RMAF.minimalVertices [1, 1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[], [false], [true], [true, false], [true, true], [true, true, false]] := by decide
#print axioms GraphCorpus_294
theorem GraphCorpus_295 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_295
theorem GraphCorpus_296 : RMAF.minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
#print axioms GraphCorpus_296
theorem GraphCorpus_297 : RMAF.minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
#print axioms GraphCorpus_297
theorem GraphCorpus_298 : RMAF.minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_298
theorem GraphCorpus_299 : RMAF.minimalVertices [0, 1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_299
theorem GraphCorpus_300 : RMAF.minimalVertices [2] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
#print axioms GraphCorpus_300
theorem GraphCorpus_301 : RMAF.minimalVertices [0, 0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
#print axioms GraphCorpus_301
theorem GraphCorpus_302 : RMAF.minimalVertices [1, 1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_302
theorem GraphCorpus_303 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[], [false], [true], [true, false], [true, true], [true, true, false], [true, true, true]] := by decide
#print axioms GraphCorpus_303
theorem GraphCorpus_304 : RMAF.minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_304
theorem GraphCorpus_305 : RMAF.minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_305
theorem GraphCorpus_306 : RMAF.minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_306
theorem GraphCorpus_307 : RMAF.minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_307
theorem GraphCorpus_308 : RMAF.minimalVertices [2] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_308
theorem GraphCorpus_309 : RMAF.minimalVertices [0, 0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_309
theorem GraphCorpus_310 : RMAF.minimalVertices [1, 1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_310
theorem GraphCorpus_311 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_311
theorem GraphCorpus_312 : RMAF.minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_312
theorem GraphCorpus_313 : RMAF.minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true]] := by decide
#print axioms GraphCorpus_313
theorem GraphCorpus_314 : RMAF.minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[true, true]] := by decide
#print axioms GraphCorpus_314
theorem GraphCorpus_315 : RMAF.minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_315
theorem GraphCorpus_316 : RMAF.minimalVertices [2] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_316
theorem GraphCorpus_317 : RMAF.minimalVertices [0, 0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true]] := by decide
#print axioms GraphCorpus_317
theorem GraphCorpus_318 : RMAF.minimalVertices [1, 1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[true, true]] := by decide
#print axioms GraphCorpus_318
theorem GraphCorpus_319 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_319
theorem GraphCorpus_320 : RMAF.minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_320
theorem GraphCorpus_321 : RMAF.minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false], [true, true]] := by decide
#print axioms GraphCorpus_321
theorem GraphCorpus_322 : RMAF.minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[true, false, true]] := by decide
#print axioms GraphCorpus_322
theorem GraphCorpus_323 : RMAF.minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_323
theorem GraphCorpus_324 : RMAF.minimalVertices [2] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_324
theorem GraphCorpus_325 : RMAF.minimalVertices [0, 0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false], [true, true]] := by decide
#print axioms GraphCorpus_325
theorem GraphCorpus_326 : RMAF.minimalVertices [1, 1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[true, false, true]] := by decide
#print axioms GraphCorpus_326
theorem GraphCorpus_327 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_327
theorem GraphCorpus_328 : RMAF.minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_328
theorem GraphCorpus_329 : RMAF.minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false]] := by decide
#print axioms GraphCorpus_329
theorem GraphCorpus_330 : RMAF.minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[true], [true, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_330
theorem GraphCorpus_331 : RMAF.minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_331
theorem GraphCorpus_332 : RMAF.minimalVertices [2] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_332
theorem GraphCorpus_333 : RMAF.minimalVertices [0, 0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false]] := by decide
#print axioms GraphCorpus_333
theorem GraphCorpus_334 : RMAF.minimalVertices [1, 1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[true], [true, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_334
theorem GraphCorpus_335 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_335
theorem GraphCorpus_336 : RMAF.minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_336
theorem GraphCorpus_337 : RMAF.minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_337
theorem GraphCorpus_338 : RMAF.minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[true, false, false]] := by decide
#print axioms GraphCorpus_338
theorem GraphCorpus_339 : RMAF.minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_339
theorem GraphCorpus_340 : RMAF.minimalVertices [2] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_340
theorem GraphCorpus_341 : RMAF.minimalVertices [0, 0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_341
theorem GraphCorpus_342 : RMAF.minimalVertices [1, 1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[true, false, false]] := by decide
#print axioms GraphCorpus_342
theorem GraphCorpus_343 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_343
theorem GraphCorpus_344 : RMAF.minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_344
theorem GraphCorpus_345 : RMAF.minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, true]] := by decide
#print axioms GraphCorpus_345
theorem GraphCorpus_346 : RMAF.minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[true], [true, false], [true, false, false], [true, true]] := by decide
#print axioms GraphCorpus_346
theorem GraphCorpus_347 : RMAF.minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_347
theorem GraphCorpus_348 : RMAF.minimalVertices [2] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_348
theorem GraphCorpus_349 : RMAF.minimalVertices [0, 0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, true]] := by decide
#print axioms GraphCorpus_349
theorem GraphCorpus_350 : RMAF.minimalVertices [1, 1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[true], [true, false], [true, false, false], [true, true]] := by decide
#print axioms GraphCorpus_350
theorem GraphCorpus_351 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_351
theorem GraphCorpus_352 : RMAF.minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_352
theorem GraphCorpus_353 : RMAF.minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[], [false], [true], [true, true]] := by decide
#print axioms GraphCorpus_353
theorem GraphCorpus_354 : RMAF.minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[true, false], [true, false, false], [true, false, true]] := by decide
#print axioms GraphCorpus_354
theorem GraphCorpus_355 : RMAF.minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_355
theorem GraphCorpus_356 : RMAF.minimalVertices [2] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_356
theorem GraphCorpus_357 : RMAF.minimalVertices [0, 0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[], [false], [true], [true, true]] := by decide
#print axioms GraphCorpus_357
theorem GraphCorpus_358 : RMAF.minimalVertices [1, 1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[true, false], [true, false, false], [true, false, true]] := by decide
#print axioms GraphCorpus_358
theorem GraphCorpus_359 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_359
theorem GraphCorpus_360 : RMAF.minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_360
theorem GraphCorpus_361 : RMAF.minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[false]] := by decide
#print axioms GraphCorpus_361
theorem GraphCorpus_362 : RMAF.minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_362
theorem GraphCorpus_363 : RMAF.minimalVertices [0, 1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_363
theorem GraphCorpus_364 : RMAF.minimalVertices [2] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_364
theorem GraphCorpus_365 : RMAF.minimalVertices [0, 0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[false]] := by decide
#print axioms GraphCorpus_365
theorem GraphCorpus_366 : RMAF.minimalVertices [1, 1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_366
theorem GraphCorpus_367 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_367
theorem GraphCorpus_368 : RMAF.minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_368
theorem GraphCorpus_369 : RMAF.minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_369
theorem GraphCorpus_370 : RMAF.minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[false]] := by decide
#print axioms GraphCorpus_370
theorem GraphCorpus_371 : RMAF.minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_371
theorem GraphCorpus_372 : RMAF.minimalVertices [2] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_372
theorem GraphCorpus_373 : RMAF.minimalVertices [0, 0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_373
theorem GraphCorpus_374 : RMAF.minimalVertices [1, 1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[false]] := by decide
#print axioms GraphCorpus_374
theorem GraphCorpus_375 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_375
theorem GraphCorpus_376 : RMAF.minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_376
theorem GraphCorpus_377 : RMAF.minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[true, false], [true, false, false], [true, false, true]] := by decide
#print axioms GraphCorpus_377
theorem GraphCorpus_378 : RMAF.minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[], [false], [true], [true, true]] := by decide
#print axioms GraphCorpus_378
theorem GraphCorpus_379 : RMAF.minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_379
theorem GraphCorpus_380 : RMAF.minimalVertices [2] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_380
theorem GraphCorpus_381 : RMAF.minimalVertices [0, 0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[true, false], [true, false, false], [true, false, true]] := by decide
#print axioms GraphCorpus_381
theorem GraphCorpus_382 : RMAF.minimalVertices [1, 1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[], [false], [true], [true, true]] := by decide
#print axioms GraphCorpus_382
theorem GraphCorpus_383 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_383
theorem GraphCorpus_384 : RMAF.minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_384
theorem GraphCorpus_385 : RMAF.minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[true], [true, false], [true, false, false], [true, true]] := by decide
#print axioms GraphCorpus_385
theorem GraphCorpus_386 : RMAF.minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, true]] := by decide
#print axioms GraphCorpus_386
theorem GraphCorpus_387 : RMAF.minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_387
theorem GraphCorpus_388 : RMAF.minimalVertices [2] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_388
theorem GraphCorpus_389 : RMAF.minimalVertices [0, 0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[true], [true, false], [true, false, false], [true, true]] := by decide
#print axioms GraphCorpus_389
theorem GraphCorpus_390 : RMAF.minimalVertices [1, 1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, true]] := by decide
#print axioms GraphCorpus_390
theorem GraphCorpus_391 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_391
theorem GraphCorpus_392 : RMAF.minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_392
theorem GraphCorpus_393 : RMAF.minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[true, false, false]] := by decide
#print axioms GraphCorpus_393
theorem GraphCorpus_394 : RMAF.minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_394
theorem GraphCorpus_395 : RMAF.minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_395
theorem GraphCorpus_396 : RMAF.minimalVertices [2] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_396
theorem GraphCorpus_397 : RMAF.minimalVertices [0, 0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[true, false, false]] := by decide
#print axioms GraphCorpus_397
theorem GraphCorpus_398 : RMAF.minimalVertices [1, 1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_398
theorem GraphCorpus_399 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_399
theorem GraphCorpus_400 : RMAF.minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_400
theorem GraphCorpus_401 : RMAF.minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[true], [true, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_401
theorem GraphCorpus_402 : RMAF.minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false]] := by decide
#print axioms GraphCorpus_402
theorem GraphCorpus_403 : RMAF.minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_403
theorem GraphCorpus_404 : RMAF.minimalVertices [2] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_404
theorem GraphCorpus_405 : RMAF.minimalVertices [0, 0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[true], [true, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_405
theorem GraphCorpus_406 : RMAF.minimalVertices [1, 1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false]] := by decide
#print axioms GraphCorpus_406
theorem GraphCorpus_407 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_407
theorem GraphCorpus_408 : RMAF.minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_408
theorem GraphCorpus_409 : RMAF.minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[true, false, true]] := by decide
#print axioms GraphCorpus_409
theorem GraphCorpus_410 : RMAF.minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false], [true, true]] := by decide
#print axioms GraphCorpus_410
theorem GraphCorpus_411 : RMAF.minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_411
theorem GraphCorpus_412 : RMAF.minimalVertices [2] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_412
theorem GraphCorpus_413 : RMAF.minimalVertices [0, 0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[true, false, true]] := by decide
#print axioms GraphCorpus_413
theorem GraphCorpus_414 : RMAF.minimalVertices [1, 1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false], [true, true]] := by decide
#print axioms GraphCorpus_414
theorem GraphCorpus_415 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_415
theorem GraphCorpus_416 : RMAF.minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_416
theorem GraphCorpus_417 : RMAF.minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[true, true]] := by decide
#print axioms GraphCorpus_417
theorem GraphCorpus_418 : RMAF.minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true]] := by decide
#print axioms GraphCorpus_418
theorem GraphCorpus_419 : RMAF.minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_419
theorem GraphCorpus_420 : RMAF.minimalVertices [2] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_420
theorem GraphCorpus_421 : RMAF.minimalVertices [0, 0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[true, true]] := by decide
#print axioms GraphCorpus_421
theorem GraphCorpus_422 : RMAF.minimalVertices [1, 1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true]] := by decide
#print axioms GraphCorpus_422
theorem GraphCorpus_423 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_423
theorem GraphCorpus_424 : RMAF.minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_424
theorem GraphCorpus_425 : RMAF.minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_425
theorem GraphCorpus_426 : RMAF.minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_426
theorem GraphCorpus_427 : RMAF.minimalVertices [0, 1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_427
theorem GraphCorpus_428 : RMAF.minimalVertices [2] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_428
theorem GraphCorpus_429 : RMAF.minimalVertices [0, 0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_429
theorem GraphCorpus_430 : RMAF.minimalVertices [1, 1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_430
theorem GraphCorpus_431 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[], [false], [true], [true, false], [true, false, false], [true, false, true], [true, true]] := by decide
#print axioms GraphCorpus_431
theorem GraphCorpus_432 : RMAF.minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_432
theorem GraphCorpus_433 : RMAF.minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_433
theorem GraphCorpus_434 : RMAF.minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_434
theorem GraphCorpus_435 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_435
theorem GraphCorpus_436 : RMAF.minimalVertices [2] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_436
theorem GraphCorpus_437 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_437
theorem GraphCorpus_438 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_438
theorem GraphCorpus_439 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_439
theorem GraphCorpus_440 : RMAF.minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_440
theorem GraphCorpus_441 : RMAF.minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, false]] := by decide
#print axioms GraphCorpus_441
theorem GraphCorpus_442 : RMAF.minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[true, true]] := by decide
#print axioms GraphCorpus_442
theorem GraphCorpus_443 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_443
theorem GraphCorpus_444 : RMAF.minimalVertices [2] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_444
theorem GraphCorpus_445 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, false]] := by decide
#print axioms GraphCorpus_445
theorem GraphCorpus_446 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[true, true]] := by decide
#print axioms GraphCorpus_446
theorem GraphCorpus_447 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_447
theorem GraphCorpus_448 : RMAF.minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_448
theorem GraphCorpus_449 : RMAF.minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[], [false], [false, false], [false, true], [true], [true, true]] := by decide
#print axioms GraphCorpus_449
theorem GraphCorpus_450 : RMAF.minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[true, false]] := by decide
#print axioms GraphCorpus_450
theorem GraphCorpus_451 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_451
theorem GraphCorpus_452 : RMAF.minimalVertices [2] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_452
theorem GraphCorpus_453 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[], [false], [false, false], [false, true], [true], [true, true]] := by decide
#print axioms GraphCorpus_453
theorem GraphCorpus_454 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[true, false]] := by decide
#print axioms GraphCorpus_454
theorem GraphCorpus_455 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_455
theorem GraphCorpus_456 : RMAF.minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_456
theorem GraphCorpus_457 : RMAF.minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[false], [false, false], [false, true]] := by decide
#print axioms GraphCorpus_457
theorem GraphCorpus_458 : RMAF.minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_458
theorem GraphCorpus_459 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_459
theorem GraphCorpus_460 : RMAF.minimalVertices [2] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_460
theorem GraphCorpus_461 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[false], [false, false], [false, true]] := by decide
#print axioms GraphCorpus_461
theorem GraphCorpus_462 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_462
theorem GraphCorpus_463 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_463
theorem GraphCorpus_464 : RMAF.minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_464
theorem GraphCorpus_465 : RMAF.minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[], [false], [false, false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_465
theorem GraphCorpus_466 : RMAF.minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[false, true]] := by decide
#print axioms GraphCorpus_466
theorem GraphCorpus_467 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_467
theorem GraphCorpus_468 : RMAF.minimalVertices [2] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_468
theorem GraphCorpus_469 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[], [false], [false, false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_469
theorem GraphCorpus_470 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[false, true]] := by decide
#print axioms GraphCorpus_470
theorem GraphCorpus_471 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_471
theorem GraphCorpus_472 : RMAF.minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_472
theorem GraphCorpus_473 : RMAF.minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[], [false], [false, false], [true], [true, false]] := by decide
#print axioms GraphCorpus_473
theorem GraphCorpus_474 : RMAF.minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[], [false], [false, true], [true], [true, true]] := by decide
#print axioms GraphCorpus_474
theorem GraphCorpus_475 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_475
theorem GraphCorpus_476 : RMAF.minimalVertices [2] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_476
theorem GraphCorpus_477 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[], [false], [false, false], [true], [true, false]] := by decide
#print axioms GraphCorpus_477
theorem GraphCorpus_478 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[], [false], [false, true], [true], [true, true]] := by decide
#print axioms GraphCorpus_478
theorem GraphCorpus_479 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_479
theorem GraphCorpus_480 : RMAF.minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_480
theorem GraphCorpus_481 : RMAF.minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[], [false], [false, false], [true], [true, true]] := by decide
#print axioms GraphCorpus_481
theorem GraphCorpus_482 : RMAF.minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[], [false], [false, true], [true], [true, false]] := by decide
#print axioms GraphCorpus_482
theorem GraphCorpus_483 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_483
theorem GraphCorpus_484 : RMAF.minimalVertices [2] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_484
theorem GraphCorpus_485 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[], [false], [false, false], [true], [true, true]] := by decide
#print axioms GraphCorpus_485
theorem GraphCorpus_486 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[], [false], [false, true], [true], [true, false]] := by decide
#print axioms GraphCorpus_486
theorem GraphCorpus_487 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_487
theorem GraphCorpus_488 : RMAF.minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_488
theorem GraphCorpus_489 : RMAF.minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[false, false]] := by decide
#print axioms GraphCorpus_489
theorem GraphCorpus_490 : RMAF.minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[], [false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_490
theorem GraphCorpus_491 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_491
theorem GraphCorpus_492 : RMAF.minimalVertices [2] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_492
theorem GraphCorpus_493 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[false, false]] := by decide
#print axioms GraphCorpus_493
theorem GraphCorpus_494 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[], [false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_494
theorem GraphCorpus_495 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_495
theorem GraphCorpus_496 : RMAF.minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_496
theorem GraphCorpus_497 : RMAF.minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[], [false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_497
theorem GraphCorpus_498 : RMAF.minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[false, false]] := by decide
#print axioms GraphCorpus_498
theorem GraphCorpus_499 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_499
theorem GraphCorpus_500 : RMAF.minimalVertices [2] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_500
theorem GraphCorpus_501 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[], [false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_501
theorem GraphCorpus_502 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[false, false]] := by decide
#print axioms GraphCorpus_502
theorem GraphCorpus_503 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_503
theorem GraphCorpus_504 : RMAF.minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_504
theorem GraphCorpus_505 : RMAF.minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[], [false], [false, true], [true], [true, false]] := by decide
#print axioms GraphCorpus_505
theorem GraphCorpus_506 : RMAF.minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[], [false], [false, false], [true], [true, true]] := by decide
#print axioms GraphCorpus_506
theorem GraphCorpus_507 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_507
theorem GraphCorpus_508 : RMAF.minimalVertices [2] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_508
theorem GraphCorpus_509 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[], [false], [false, true], [true], [true, false]] := by decide
#print axioms GraphCorpus_509
theorem GraphCorpus_510 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[], [false], [false, false], [true], [true, true]] := by decide
#print axioms GraphCorpus_510
theorem GraphCorpus_511 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_511
theorem GraphCorpus_512 : RMAF.minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_512
theorem GraphCorpus_513 : RMAF.minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[], [false], [false, true], [true], [true, true]] := by decide
#print axioms GraphCorpus_513
theorem GraphCorpus_514 : RMAF.minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[], [false], [false, false], [true], [true, false]] := by decide
#print axioms GraphCorpus_514
theorem GraphCorpus_515 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_515
theorem GraphCorpus_516 : RMAF.minimalVertices [2] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_516
theorem GraphCorpus_517 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[], [false], [false, true], [true], [true, true]] := by decide
#print axioms GraphCorpus_517
theorem GraphCorpus_518 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[], [false], [false, false], [true], [true, false]] := by decide
#print axioms GraphCorpus_518
theorem GraphCorpus_519 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_519
theorem GraphCorpus_520 : RMAF.minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_520
theorem GraphCorpus_521 : RMAF.minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[false, true]] := by decide
#print axioms GraphCorpus_521
theorem GraphCorpus_522 : RMAF.minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[], [false], [false, false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_522
theorem GraphCorpus_523 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_523
theorem GraphCorpus_524 : RMAF.minimalVertices [2] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_524
theorem GraphCorpus_525 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[false, true]] := by decide
#print axioms GraphCorpus_525
theorem GraphCorpus_526 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[], [false], [false, false], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_526
theorem GraphCorpus_527 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_527
theorem GraphCorpus_528 : RMAF.minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_528
theorem GraphCorpus_529 : RMAF.minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_529
theorem GraphCorpus_530 : RMAF.minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[false], [false, false], [false, true]] := by decide
#print axioms GraphCorpus_530
theorem GraphCorpus_531 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_531
theorem GraphCorpus_532 : RMAF.minimalVertices [2] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_532
theorem GraphCorpus_533 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_533
theorem GraphCorpus_534 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[false], [false, false], [false, true]] := by decide
#print axioms GraphCorpus_534
theorem GraphCorpus_535 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_535
theorem GraphCorpus_536 : RMAF.minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_536
theorem GraphCorpus_537 : RMAF.minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[true, false]] := by decide
#print axioms GraphCorpus_537
theorem GraphCorpus_538 : RMAF.minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, true]] := by decide
#print axioms GraphCorpus_538
theorem GraphCorpus_539 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_539
theorem GraphCorpus_540 : RMAF.minimalVertices [2] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_540
theorem GraphCorpus_541 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[true, false]] := by decide
#print axioms GraphCorpus_541
theorem GraphCorpus_542 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, true]] := by decide
#print axioms GraphCorpus_542
theorem GraphCorpus_543 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_543
theorem GraphCorpus_544 : RMAF.minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_544
theorem GraphCorpus_545 : RMAF.minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[true, true]] := by decide
#print axioms GraphCorpus_545
theorem GraphCorpus_546 : RMAF.minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[], [false], [false, false], [false, true], [true], [true, false]] := by decide
#print axioms GraphCorpus_546
theorem GraphCorpus_547 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_547
theorem GraphCorpus_548 : RMAF.minimalVertices [2] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms GraphCorpus_548
theorem GraphCorpus_549 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[true, true]] := by decide
#print axioms GraphCorpus_549
theorem GraphCorpus_550 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[], [false], [false, false], [false, true], [true], [true, false]] := by decide
#print axioms GraphCorpus_550
theorem GraphCorpus_551 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_551
theorem GraphCorpus_552 : RMAF.minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_552
theorem GraphCorpus_553 : RMAF.minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_553
theorem GraphCorpus_554 : RMAF.minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_554
theorem GraphCorpus_555 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_555
theorem GraphCorpus_556 : RMAF.minimalVertices [2] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_556
theorem GraphCorpus_557 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms GraphCorpus_557
theorem GraphCorpus_558 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_558
theorem GraphCorpus_559 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by decide
#print axioms GraphCorpus_559
theorem GraphCorpus_560 : RMAF.minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_560
theorem GraphCorpus_561 : RMAF.minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_561
theorem GraphCorpus_562 : RMAF.minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_562
theorem GraphCorpus_563 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_563
theorem GraphCorpus_564 : RMAF.minimalVertices [2] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_564
theorem GraphCorpus_565 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_565
theorem GraphCorpus_566 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_566
theorem GraphCorpus_567 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_567
theorem GraphCorpus_568 : RMAF.minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_568
theorem GraphCorpus_569 : RMAF.minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[false], [false, false], [false, true], [false, true, false], [false, true, true]] := by decide
#print axioms GraphCorpus_569
theorem GraphCorpus_570 : RMAF.minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[true]] := by decide
#print axioms GraphCorpus_570
theorem GraphCorpus_571 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_571
theorem GraphCorpus_572 : RMAF.minimalVertices [2] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_572
theorem GraphCorpus_573 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[false], [false, false], [false, true], [false, true, false], [false, true, true]] := by decide
#print axioms GraphCorpus_573
theorem GraphCorpus_574 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[true]] := by decide
#print axioms GraphCorpus_574
theorem GraphCorpus_575 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_575
theorem GraphCorpus_576 : RMAF.minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_576
theorem GraphCorpus_577 : RMAF.minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[], [false], [false, false], [false, true], [false, true, false], [true]] := by decide
#print axioms GraphCorpus_577
theorem GraphCorpus_578 : RMAF.minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[false, true, true]] := by decide
#print axioms GraphCorpus_578
theorem GraphCorpus_579 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_579
theorem GraphCorpus_580 : RMAF.minimalVertices [2] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_580
theorem GraphCorpus_581 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[], [false], [false, false], [false, true], [false, true, false], [true]] := by decide
#print axioms GraphCorpus_581
theorem GraphCorpus_582 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[false, true, true]] := by decide
#print axioms GraphCorpus_582
theorem GraphCorpus_583 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_583
theorem GraphCorpus_584 : RMAF.minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_584
theorem GraphCorpus_585 : RMAF.minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[false], [false, false], [false, true], [false, true, false]] := by decide
#print axioms GraphCorpus_585
theorem GraphCorpus_586 : RMAF.minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[], [false], [false, true], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_586
theorem GraphCorpus_587 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_587
theorem GraphCorpus_588 : RMAF.minimalVertices [2] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_588
theorem GraphCorpus_589 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[false], [false, false], [false, true], [false, true, false]] := by decide
#print axioms GraphCorpus_589
theorem GraphCorpus_590 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[], [false], [false, true], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_590
theorem GraphCorpus_591 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_591
theorem GraphCorpus_592 : RMAF.minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_592
theorem GraphCorpus_593 : RMAF.minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[], [false], [false, false], [false, true], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_593
theorem GraphCorpus_594 : RMAF.minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[false, true, false]] := by decide
#print axioms GraphCorpus_594
theorem GraphCorpus_595 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_595
theorem GraphCorpus_596 : RMAF.minimalVertices [2] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_596
theorem GraphCorpus_597 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[], [false], [false, false], [false, true], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_597
theorem GraphCorpus_598 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[false, true, false]] := by decide
#print axioms GraphCorpus_598
theorem GraphCorpus_599 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_599
theorem GraphCorpus_600 : RMAF.minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_600
theorem GraphCorpus_601 : RMAF.minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[false], [false, false], [false, true], [false, true, true]] := by decide
#print axioms GraphCorpus_601
theorem GraphCorpus_602 : RMAF.minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[], [false], [false, true], [false, true, false], [true]] := by decide
#print axioms GraphCorpus_602
theorem GraphCorpus_603 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_603
theorem GraphCorpus_604 : RMAF.minimalVertices [2] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_604
theorem GraphCorpus_605 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[false], [false, false], [false, true], [false, true, true]] := by decide
#print axioms GraphCorpus_605
theorem GraphCorpus_606 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[], [false], [false, true], [false, true, false], [true]] := by decide
#print axioms GraphCorpus_606
theorem GraphCorpus_607 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_607
theorem GraphCorpus_608 : RMAF.minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_608
theorem GraphCorpus_609 : RMAF.minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[], [false], [false, false], [true]] := by decide
#print axioms GraphCorpus_609
theorem GraphCorpus_610 : RMAF.minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[false, true], [false, true, false], [false, true, true]] := by decide
#print axioms GraphCorpus_610
theorem GraphCorpus_611 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_611
theorem GraphCorpus_612 : RMAF.minimalVertices [2] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_612
theorem GraphCorpus_613 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[], [false], [false, false], [true]] := by decide
#print axioms GraphCorpus_613
theorem GraphCorpus_614 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[false, true], [false, true, false], [false, true, true]] := by decide
#print axioms GraphCorpus_614
theorem GraphCorpus_615 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_615
theorem GraphCorpus_616 : RMAF.minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_616
theorem GraphCorpus_617 : RMAF.minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[false, false]] := by decide
#print axioms GraphCorpus_617
theorem GraphCorpus_618 : RMAF.minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[], [false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_618
theorem GraphCorpus_619 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_619
theorem GraphCorpus_620 : RMAF.minimalVertices [2] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_620
theorem GraphCorpus_621 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[false, false]] := by decide
#print axioms GraphCorpus_621
theorem GraphCorpus_622 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[], [false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_622
theorem GraphCorpus_623 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_623
theorem GraphCorpus_624 : RMAF.minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_624
theorem GraphCorpus_625 : RMAF.minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[], [false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_625
theorem GraphCorpus_626 : RMAF.minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[false, false]] := by decide
#print axioms GraphCorpus_626
theorem GraphCorpus_627 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_627
theorem GraphCorpus_628 : RMAF.minimalVertices [2] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_628
theorem GraphCorpus_629 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[], [false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_629
theorem GraphCorpus_630 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[false, false]] := by decide
#print axioms GraphCorpus_630
theorem GraphCorpus_631 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_631
theorem GraphCorpus_632 : RMAF.minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_632
theorem GraphCorpus_633 : RMAF.minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[false, true], [false, true, false], [false, true, true]] := by decide
#print axioms GraphCorpus_633
theorem GraphCorpus_634 : RMAF.minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[], [false], [false, false], [true]] := by decide
#print axioms GraphCorpus_634
theorem GraphCorpus_635 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_635
theorem GraphCorpus_636 : RMAF.minimalVertices [2] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_636
theorem GraphCorpus_637 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[false, true], [false, true, false], [false, true, true]] := by decide
#print axioms GraphCorpus_637
theorem GraphCorpus_638 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[], [false], [false, false], [true]] := by decide
#print axioms GraphCorpus_638
theorem GraphCorpus_639 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_639
theorem GraphCorpus_640 : RMAF.minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_640
theorem GraphCorpus_641 : RMAF.minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[], [false], [false, true], [false, true, false], [true]] := by decide
#print axioms GraphCorpus_641
theorem GraphCorpus_642 : RMAF.minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[false], [false, false], [false, true], [false, true, true]] := by decide
#print axioms GraphCorpus_642
theorem GraphCorpus_643 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_643
theorem GraphCorpus_644 : RMAF.minimalVertices [2] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_644
theorem GraphCorpus_645 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[], [false], [false, true], [false, true, false], [true]] := by decide
#print axioms GraphCorpus_645
theorem GraphCorpus_646 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[false], [false, false], [false, true], [false, true, true]] := by decide
#print axioms GraphCorpus_646
theorem GraphCorpus_647 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_647
theorem GraphCorpus_648 : RMAF.minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_648
theorem GraphCorpus_649 : RMAF.minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[false, true, false]] := by decide
#print axioms GraphCorpus_649
theorem GraphCorpus_650 : RMAF.minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[], [false], [false, false], [false, true], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_650
theorem GraphCorpus_651 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_651
theorem GraphCorpus_652 : RMAF.minimalVertices [2] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_652
theorem GraphCorpus_653 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[false, true, false]] := by decide
#print axioms GraphCorpus_653
theorem GraphCorpus_654 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[], [false], [false, false], [false, true], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_654
theorem GraphCorpus_655 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_655
theorem GraphCorpus_656 : RMAF.minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_656
theorem GraphCorpus_657 : RMAF.minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[], [false], [false, true], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_657
theorem GraphCorpus_658 : RMAF.minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[false], [false, false], [false, true], [false, true, false]] := by decide
#print axioms GraphCorpus_658
theorem GraphCorpus_659 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_659
theorem GraphCorpus_660 : RMAF.minimalVertices [2] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_660
theorem GraphCorpus_661 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[], [false], [false, true], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_661
theorem GraphCorpus_662 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[false], [false, false], [false, true], [false, true, false]] := by decide
#print axioms GraphCorpus_662
theorem GraphCorpus_663 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_663
theorem GraphCorpus_664 : RMAF.minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_664
theorem GraphCorpus_665 : RMAF.minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[false, true, true]] := by decide
#print axioms GraphCorpus_665
theorem GraphCorpus_666 : RMAF.minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[], [false], [false, false], [false, true], [false, true, false], [true]] := by decide
#print axioms GraphCorpus_666
theorem GraphCorpus_667 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_667
theorem GraphCorpus_668 : RMAF.minimalVertices [2] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_668
theorem GraphCorpus_669 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[false, true, true]] := by decide
#print axioms GraphCorpus_669
theorem GraphCorpus_670 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[], [false], [false, false], [false, true], [false, true, false], [true]] := by decide
#print axioms GraphCorpus_670
theorem GraphCorpus_671 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_671
theorem GraphCorpus_672 : RMAF.minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_672
theorem GraphCorpus_673 : RMAF.minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[true]] := by decide
#print axioms GraphCorpus_673
theorem GraphCorpus_674 : RMAF.minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[false], [false, false], [false, true], [false, true, false], [false, true, true]] := by decide
#print axioms GraphCorpus_674
theorem GraphCorpus_675 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_675
theorem GraphCorpus_676 : RMAF.minimalVertices [2] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_676
theorem GraphCorpus_677 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[true]] := by decide
#print axioms GraphCorpus_677
theorem GraphCorpus_678 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[false], [false, false], [false, true], [false, true, false], [false, true, true]] := by decide
#print axioms GraphCorpus_678
theorem GraphCorpus_679 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_679
theorem GraphCorpus_680 : RMAF.minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_680
theorem GraphCorpus_681 : RMAF.minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_681
theorem GraphCorpus_682 : RMAF.minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_682
theorem GraphCorpus_683 : RMAF.minimalVertices [0, 1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_683
theorem GraphCorpus_684 : RMAF.minimalVertices [2] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_684
theorem GraphCorpus_685 : RMAF.minimalVertices [0, 0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_685
theorem GraphCorpus_686 : RMAF.minimalVertices [1, 1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_686
theorem GraphCorpus_687 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[], [false], [false, false], [false, true], [false, true, false], [false, true, true], [true]] := by decide
#print axioms GraphCorpus_687
theorem GraphCorpus_688 : RMAF.minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_688
theorem GraphCorpus_689 : RMAF.minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_689
theorem GraphCorpus_690 : RMAF.minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_690
theorem GraphCorpus_691 : RMAF.minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_691
theorem GraphCorpus_692 : RMAF.minimalVertices [2] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_692
theorem GraphCorpus_693 : RMAF.minimalVertices [0, 0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_693
theorem GraphCorpus_694 : RMAF.minimalVertices [1, 1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_694
theorem GraphCorpus_695 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_695
theorem GraphCorpus_696 : RMAF.minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_696
theorem GraphCorpus_697 : RMAF.minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[false], [false, false], [false, false, false], [false, false, true], [false, true]] := by decide
#print axioms GraphCorpus_697
theorem GraphCorpus_698 : RMAF.minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[true]] := by decide
#print axioms GraphCorpus_698
theorem GraphCorpus_699 : RMAF.minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_699
theorem GraphCorpus_700 : RMAF.minimalVertices [2] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_700
theorem GraphCorpus_701 : RMAF.minimalVertices [0, 0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[false], [false, false], [false, false, false], [false, false, true], [false, true]] := by decide
#print axioms GraphCorpus_701
theorem GraphCorpus_702 : RMAF.minimalVertices [1, 1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[true]] := by decide
#print axioms GraphCorpus_702
theorem GraphCorpus_703 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_703
theorem GraphCorpus_704 : RMAF.minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_704
theorem GraphCorpus_705 : RMAF.minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [false, false, true], [true]] := by decide
#print axioms GraphCorpus_705
theorem GraphCorpus_706 : RMAF.minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[false, true]] := by decide
#print axioms GraphCorpus_706
theorem GraphCorpus_707 : RMAF.minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_707
theorem GraphCorpus_708 : RMAF.minimalVertices [2] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_708
theorem GraphCorpus_709 : RMAF.minimalVertices [0, 0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [false, false, true], [true]] := by decide
#print axioms GraphCorpus_709
theorem GraphCorpus_710 : RMAF.minimalVertices [1, 1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[false, true]] := by decide
#print axioms GraphCorpus_710
theorem GraphCorpus_711 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_711
theorem GraphCorpus_712 : RMAF.minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_712
theorem GraphCorpus_713 : RMAF.minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[false, false], [false, false, false], [false, false, true]] := by decide
#print axioms GraphCorpus_713
theorem GraphCorpus_714 : RMAF.minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[], [false], [false, true], [true]] := by decide
#print axioms GraphCorpus_714
theorem GraphCorpus_715 : RMAF.minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_715
theorem GraphCorpus_716 : RMAF.minimalVertices [2] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_716
theorem GraphCorpus_717 : RMAF.minimalVertices [0, 0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[false, false], [false, false, false], [false, false, true]] := by decide
#print axioms GraphCorpus_717
theorem GraphCorpus_718 : RMAF.minimalVertices [1, 1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[], [false], [false, true], [true]] := by decide
#print axioms GraphCorpus_718
theorem GraphCorpus_719 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_719
theorem GraphCorpus_720 : RMAF.minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_720
theorem GraphCorpus_721 : RMAF.minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_721
theorem GraphCorpus_722 : RMAF.minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[false, false, true]] := by decide
#print axioms GraphCorpus_722
theorem GraphCorpus_723 : RMAF.minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_723
theorem GraphCorpus_724 : RMAF.minimalVertices [2] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_724
theorem GraphCorpus_725 : RMAF.minimalVertices [0, 0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_725
theorem GraphCorpus_726 : RMAF.minimalVertices [1, 1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[false, false, true]] := by decide
#print axioms GraphCorpus_726
theorem GraphCorpus_727 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_727
theorem GraphCorpus_728 : RMAF.minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_728
theorem GraphCorpus_729 : RMAF.minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[false], [false, false], [false, false, false], [false, true]] := by decide
#print axioms GraphCorpus_729
theorem GraphCorpus_730 : RMAF.minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[], [false], [false, false], [false, false, true], [true]] := by decide
#print axioms GraphCorpus_730
theorem GraphCorpus_731 : RMAF.minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_731
theorem GraphCorpus_732 : RMAF.minimalVertices [2] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_732
theorem GraphCorpus_733 : RMAF.minimalVertices [0, 0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[false], [false, false], [false, false, false], [false, true]] := by decide
#print axioms GraphCorpus_733
theorem GraphCorpus_734 : RMAF.minimalVertices [1, 1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[], [false], [false, false], [false, false, true], [true]] := by decide
#print axioms GraphCorpus_734
theorem GraphCorpus_735 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_735
theorem GraphCorpus_736 : RMAF.minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_736
theorem GraphCorpus_737 : RMAF.minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [true]] := by decide
#print axioms GraphCorpus_737
theorem GraphCorpus_738 : RMAF.minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[false], [false, false], [false, false, true], [false, true]] := by decide
#print axioms GraphCorpus_738
theorem GraphCorpus_739 : RMAF.minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_739
theorem GraphCorpus_740 : RMAF.minimalVertices [2] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_740
theorem GraphCorpus_741 : RMAF.minimalVertices [0, 0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [true]] := by decide
#print axioms GraphCorpus_741
theorem GraphCorpus_742 : RMAF.minimalVertices [1, 1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[false], [false, false], [false, false, true], [false, true]] := by decide
#print axioms GraphCorpus_742
theorem GraphCorpus_743 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_743
theorem GraphCorpus_744 : RMAF.minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_744
theorem GraphCorpus_745 : RMAF.minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[false, false, false]] := by decide
#print axioms GraphCorpus_745
theorem GraphCorpus_746 : RMAF.minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[], [false], [false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_746
theorem GraphCorpus_747 : RMAF.minimalVertices [0, 1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_747
theorem GraphCorpus_748 : RMAF.minimalVertices [2] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_748
theorem GraphCorpus_749 : RMAF.minimalVertices [0, 0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[false, false, false]] := by decide
#print axioms GraphCorpus_749
theorem GraphCorpus_750 : RMAF.minimalVertices [1, 1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[], [false], [false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_750
theorem GraphCorpus_751 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_751
theorem GraphCorpus_752 : RMAF.minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_752
theorem GraphCorpus_753 : RMAF.minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[], [false], [false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_753
theorem GraphCorpus_754 : RMAF.minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[false, false, false]] := by decide
#print axioms GraphCorpus_754
theorem GraphCorpus_755 : RMAF.minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_755
theorem GraphCorpus_756 : RMAF.minimalVertices [2] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_756
theorem GraphCorpus_757 : RMAF.minimalVertices [0, 0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[], [false], [false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_757
theorem GraphCorpus_758 : RMAF.minimalVertices [1, 1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[false, false, false]] := by decide
#print axioms GraphCorpus_758
theorem GraphCorpus_759 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_759
theorem GraphCorpus_760 : RMAF.minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_760
theorem GraphCorpus_761 : RMAF.minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[false], [false, false], [false, false, true], [false, true]] := by decide
#print axioms GraphCorpus_761
theorem GraphCorpus_762 : RMAF.minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [true]] := by decide
#print axioms GraphCorpus_762
theorem GraphCorpus_763 : RMAF.minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_763
theorem GraphCorpus_764 : RMAF.minimalVertices [2] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_764
theorem GraphCorpus_765 : RMAF.minimalVertices [0, 0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[false], [false, false], [false, false, true], [false, true]] := by decide
#print axioms GraphCorpus_765
theorem GraphCorpus_766 : RMAF.minimalVertices [1, 1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [true]] := by decide
#print axioms GraphCorpus_766
theorem GraphCorpus_767 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_767
theorem GraphCorpus_768 : RMAF.minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_768
theorem GraphCorpus_769 : RMAF.minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[], [false], [false, false], [false, false, true], [true]] := by decide
#print axioms GraphCorpus_769
theorem GraphCorpus_770 : RMAF.minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[false], [false, false], [false, false, false], [false, true]] := by decide
#print axioms GraphCorpus_770
theorem GraphCorpus_771 : RMAF.minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_771
theorem GraphCorpus_772 : RMAF.minimalVertices [2] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_772
theorem GraphCorpus_773 : RMAF.minimalVertices [0, 0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[], [false], [false, false], [false, false, true], [true]] := by decide
#print axioms GraphCorpus_773
theorem GraphCorpus_774 : RMAF.minimalVertices [1, 1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[false], [false, false], [false, false, false], [false, true]] := by decide
#print axioms GraphCorpus_774
theorem GraphCorpus_775 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_775
theorem GraphCorpus_776 : RMAF.minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_776
theorem GraphCorpus_777 : RMAF.minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[false, false, true]] := by decide
#print axioms GraphCorpus_777
theorem GraphCorpus_778 : RMAF.minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_778
theorem GraphCorpus_779 : RMAF.minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_779
theorem GraphCorpus_780 : RMAF.minimalVertices [2] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_780
theorem GraphCorpus_781 : RMAF.minimalVertices [0, 0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[false, false, true]] := by decide
#print axioms GraphCorpus_781
theorem GraphCorpus_782 : RMAF.minimalVertices [1, 1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [false, true], [true]] := by decide
#print axioms GraphCorpus_782
theorem GraphCorpus_783 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_783
theorem GraphCorpus_784 : RMAF.minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_784
theorem GraphCorpus_785 : RMAF.minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[], [false], [false, true], [true]] := by decide
#print axioms GraphCorpus_785
theorem GraphCorpus_786 : RMAF.minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[false, false], [false, false, false], [false, false, true]] := by decide
#print axioms GraphCorpus_786
theorem GraphCorpus_787 : RMAF.minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_787
theorem GraphCorpus_788 : RMAF.minimalVertices [2] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_788
theorem GraphCorpus_789 : RMAF.minimalVertices [0, 0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[], [false], [false, true], [true]] := by decide
#print axioms GraphCorpus_789
theorem GraphCorpus_790 : RMAF.minimalVertices [1, 1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[false, false], [false, false, false], [false, false, true]] := by decide
#print axioms GraphCorpus_790
theorem GraphCorpus_791 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_791
theorem GraphCorpus_792 : RMAF.minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_792
theorem GraphCorpus_793 : RMAF.minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[false, true]] := by decide
#print axioms GraphCorpus_793
theorem GraphCorpus_794 : RMAF.minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [false, false, true], [true]] := by decide
#print axioms GraphCorpus_794
theorem GraphCorpus_795 : RMAF.minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_795
theorem GraphCorpus_796 : RMAF.minimalVertices [2] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_796
theorem GraphCorpus_797 : RMAF.minimalVertices [0, 0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[false, true]] := by decide
#print axioms GraphCorpus_797
theorem GraphCorpus_798 : RMAF.minimalVertices [1, 1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [false, false, true], [true]] := by decide
#print axioms GraphCorpus_798
theorem GraphCorpus_799 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_799
theorem GraphCorpus_800 : RMAF.minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_800
theorem GraphCorpus_801 : RMAF.minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[true]] := by decide
#print axioms GraphCorpus_801
theorem GraphCorpus_802 : RMAF.minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[false], [false, false], [false, false, false], [false, false, true], [false, true]] := by decide
#print axioms GraphCorpus_802
theorem GraphCorpus_803 : RMAF.minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_803
theorem GraphCorpus_804 : RMAF.minimalVertices [2] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms GraphCorpus_804
theorem GraphCorpus_805 : RMAF.minimalVertices [0, 0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[true]] := by decide
#print axioms GraphCorpus_805
theorem GraphCorpus_806 : RMAF.minimalVertices [1, 1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[false], [false, false], [false, false, false], [false, false, true], [false, true]] := by decide
#print axioms GraphCorpus_806
theorem GraphCorpus_807 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_807
theorem GraphCorpus_808 : RMAF.minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_808
theorem GraphCorpus_809 : RMAF.minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_809
theorem GraphCorpus_810 : RMAF.minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_810
theorem GraphCorpus_811 : RMAF.minimalVertices [0, 1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_811
theorem GraphCorpus_812 : RMAF.minimalVertices [2] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_812
theorem GraphCorpus_813 : RMAF.minimalVertices [0, 0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms GraphCorpus_813
theorem GraphCorpus_814 : RMAF.minimalVertices [1, 1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_814
theorem GraphCorpus_815 : RMAF.minimalVertices [0, 1, 0, 1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[], [false], [false, false], [false, false, false], [false, false, true], [false, true], [true]] := by decide
#print axioms GraphCorpus_815
end LeastnessAdversary
