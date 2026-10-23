import RMAF
import TreeAddresses
open RMAF LeastEmbedding
namespace FreshSourcePanel
theorem case0000 : minimalVertices [] (.leaf 0) = [] ∧ terminals [] (.leaf 0) = [] := by decide
#print axioms case0000
theorem case0001 : minimalVertices [0] (.leaf 0) = [[]] ∧ terminals [0] (.leaf 0) = [[]] := by decide
#print axioms case0001
theorem case0002 : minimalVertices [1] (.leaf 0) = [] ∧ terminals [1] (.leaf 0) = [] := by decide
#print axioms case0002
theorem case0003 : minimalVertices [0,1] (.leaf 0) = [[]] ∧ terminals [0,1] (.leaf 0) = [[]] := by decide
#print axioms case0003
theorem case0004 : minimalVertices [0,0] (.leaf 0) = [[]] ∧ terminals [0,0] (.leaf 0) = [[]] := by decide
#print axioms case0004
theorem case0005 : minimalVertices [0,1,0] (.leaf 0) = [[]] ∧ terminals [0,1,0] (.leaf 0) = [[]] := by decide
#print axioms case0005
theorem case0006 : minimalVertices [25] (.leaf 0) = [] ∧ terminals [25] (.leaf 0) = [] := by decide
#print axioms case0006
theorem case0007 : minimalVertices [] (.leaf 1) = [] ∧ terminals [] (.leaf 1) = [] := by decide
#print axioms case0007
theorem case0008 : minimalVertices [0] (.leaf 1) = [] ∧ terminals [0] (.leaf 1) = [] := by decide
#print axioms case0008
theorem case0009 : minimalVertices [1] (.leaf 1) = [[]] ∧ terminals [1] (.leaf 1) = [[]] := by decide
#print axioms case0009
theorem case0010 : minimalVertices [0,1] (.leaf 1) = [[]] ∧ terminals [0,1] (.leaf 1) = [[]] := by decide
#print axioms case0010
theorem case0011 : minimalVertices [0,0] (.leaf 1) = [] ∧ terminals [0,0] (.leaf 1) = [] := by decide
#print axioms case0011
theorem case0012 : minimalVertices [0,1,0] (.leaf 1) = [[]] ∧ terminals [0,1,0] (.leaf 1) = [[]] := by decide
#print axioms case0012
theorem case0013 : minimalVertices [25] (.leaf 1) = [] ∧ terminals [25] (.leaf 1) = [] := by decide
#print axioms case0013
theorem case0014 : minimalVertices [] (.node (.leaf 0) (.leaf 0)) = [] ∧ terminals [] (.node (.leaf 0) (.leaf 0)) = [] := by decide
#print axioms case0014
theorem case0015 : minimalVertices [0] (.node (.leaf 0) (.leaf 0)) = [[],[false],[true]] ∧ terminals [0] (.node (.leaf 0) (.leaf 0)) = [[false],[true]] := by decide
#print axioms case0015
theorem case0016 : minimalVertices [1] (.node (.leaf 0) (.leaf 0)) = [] ∧ terminals [1] (.node (.leaf 0) (.leaf 0)) = [] := by decide
#print axioms case0016
theorem case0017 : minimalVertices [0,1] (.node (.leaf 0) (.leaf 0)) = [[],[false],[true]] ∧ terminals [0,1] (.node (.leaf 0) (.leaf 0)) = [[false],[true]] := by decide
#print axioms case0017
theorem case0018 : minimalVertices [0,0] (.node (.leaf 0) (.leaf 0)) = [[],[false],[true]] ∧ terminals [0,0] (.node (.leaf 0) (.leaf 0)) = [[false],[true]] := by decide
#print axioms case0018
theorem case0019 : minimalVertices [0,1,0] (.node (.leaf 0) (.leaf 0)) = [[],[false],[true]] ∧ terminals [0,1,0] (.node (.leaf 0) (.leaf 0)) = [[false],[true]] := by decide
#print axioms case0019
theorem case0020 : minimalVertices [25] (.node (.leaf 0) (.leaf 0)) = [] ∧ terminals [25] (.node (.leaf 0) (.leaf 0)) = [] := by decide
#print axioms case0020
theorem case0021 : minimalVertices [] (.node (.leaf 0) (.leaf 1)) = [] ∧ terminals [] (.node (.leaf 0) (.leaf 1)) = [] := by decide
#print axioms case0021
theorem case0022 : minimalVertices [0] (.node (.leaf 0) (.leaf 1)) = [[false]] ∧ terminals [0] (.node (.leaf 0) (.leaf 1)) = [[false]] := by decide
#print axioms case0022
theorem case0023 : minimalVertices [1] (.node (.leaf 0) (.leaf 1)) = [[true]] ∧ terminals [1] (.node (.leaf 0) (.leaf 1)) = [[true]] := by decide
#print axioms case0023
theorem case0024 : minimalVertices [0,1] (.node (.leaf 0) (.leaf 1)) = [[],[false],[true]] ∧ terminals [0,1] (.node (.leaf 0) (.leaf 1)) = [[false],[true]] := by decide
#print axioms case0024
theorem case0025 : minimalVertices [0,0] (.node (.leaf 0) (.leaf 1)) = [[false]] ∧ terminals [0,0] (.node (.leaf 0) (.leaf 1)) = [[false]] := by decide
#print axioms case0025
theorem case0026 : minimalVertices [0,1,0] (.node (.leaf 0) (.leaf 1)) = [[],[false],[true]] ∧ terminals [0,1,0] (.node (.leaf 0) (.leaf 1)) = [[false],[true]] := by decide
#print axioms case0026
theorem case0027 : minimalVertices [25] (.node (.leaf 0) (.leaf 1)) = [] ∧ terminals [25] (.node (.leaf 0) (.leaf 1)) = [] := by decide
#print axioms case0027
theorem case0028 : minimalVertices [] (.node (.leaf 1) (.leaf 0)) = [] ∧ terminals [] (.node (.leaf 1) (.leaf 0)) = [] := by decide
#print axioms case0028
theorem case0029 : minimalVertices [0] (.node (.leaf 1) (.leaf 0)) = [[true]] ∧ terminals [0] (.node (.leaf 1) (.leaf 0)) = [[true]] := by decide
#print axioms case0029
theorem case0030 : minimalVertices [1] (.node (.leaf 1) (.leaf 0)) = [[false]] ∧ terminals [1] (.node (.leaf 1) (.leaf 0)) = [[false]] := by decide
#print axioms case0030
theorem case0031 : minimalVertices [0,1] (.node (.leaf 1) (.leaf 0)) = [[],[false],[true]] ∧ terminals [0,1] (.node (.leaf 1) (.leaf 0)) = [[false],[true]] := by decide
#print axioms case0031
theorem case0032 : minimalVertices [0,0] (.node (.leaf 1) (.leaf 0)) = [[true]] ∧ terminals [0,0] (.node (.leaf 1) (.leaf 0)) = [[true]] := by decide
#print axioms case0032
theorem case0033 : minimalVertices [0,1,0] (.node (.leaf 1) (.leaf 0)) = [[],[false],[true]] ∧ terminals [0,1,0] (.node (.leaf 1) (.leaf 0)) = [[false],[true]] := by decide
#print axioms case0033
theorem case0034 : minimalVertices [25] (.node (.leaf 1) (.leaf 0)) = [] ∧ terminals [25] (.node (.leaf 1) (.leaf 0)) = [] := by decide
#print axioms case0034
theorem case0035 : minimalVertices [] (.node (.leaf 1) (.leaf 1)) = [] ∧ terminals [] (.node (.leaf 1) (.leaf 1)) = [] := by decide
#print axioms case0035
theorem case0036 : minimalVertices [0] (.node (.leaf 1) (.leaf 1)) = [] ∧ terminals [0] (.node (.leaf 1) (.leaf 1)) = [] := by decide
#print axioms case0036
theorem case0037 : minimalVertices [1] (.node (.leaf 1) (.leaf 1)) = [[],[false],[true]] ∧ terminals [1] (.node (.leaf 1) (.leaf 1)) = [[false],[true]] := by decide
#print axioms case0037
theorem case0038 : minimalVertices [0,1] (.node (.leaf 1) (.leaf 1)) = [[],[false],[true]] ∧ terminals [0,1] (.node (.leaf 1) (.leaf 1)) = [[false],[true]] := by decide
#print axioms case0038
theorem case0039 : minimalVertices [0,0] (.node (.leaf 1) (.leaf 1)) = [] ∧ terminals [0,0] (.node (.leaf 1) (.leaf 1)) = [] := by decide
#print axioms case0039
theorem case0040 : minimalVertices [0,1,0] (.node (.leaf 1) (.leaf 1)) = [[],[false],[true]] ∧ terminals [0,1,0] (.node (.leaf 1) (.leaf 1)) = [[false],[true]] := by decide
#print axioms case0040
theorem case0041 : minimalVertices [25] (.node (.leaf 1) (.leaf 1)) = [] ∧ terminals [25] (.node (.leaf 1) (.leaf 1)) = [] := by decide
#print axioms case0041
theorem case0042 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [] ∧ terminals [] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms case0042
theorem case0043 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [[],[false],[true],[true,false],[true,true]] ∧ terminals [0] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [[false],[true,false],[true,true]] := by decide
#print axioms case0043
theorem case0044 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [] ∧ terminals [1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms case0044
theorem case0045 : minimalVertices [0,1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [[],[false],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [[false],[true,false],[true,true]] := by decide
#print axioms case0045
theorem case0046 : minimalVertices [0,0] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [[],[false],[true],[true,false],[true,true]] ∧ terminals [0,0] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [[false],[true,false],[true,true]] := by decide
#print axioms case0046
theorem case0047 : minimalVertices [0,1,0] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [[],[false],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [[false],[true,false],[true,true]] := by decide
#print axioms case0047
theorem case0048 : minimalVertices [25] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [] ∧ terminals [25] (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms case0048
theorem case0049 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [] ∧ terminals [] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms case0049
theorem case0050 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [[],[false],[true],[true,false]] ∧ terminals [0] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [[false],[true,false]] := by decide
#print axioms case0050
theorem case0051 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [[true,true]] ∧ terminals [1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [[true,true]] := by decide
#print axioms case0051
theorem case0052 : minimalVertices [0,1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [[],[false],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [[false],[true,false],[true,true]] := by decide
#print axioms case0052
theorem case0053 : minimalVertices [0,0] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [[],[false],[true],[true,false]] ∧ terminals [0,0] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [[false],[true,false]] := by decide
#print axioms case0053
theorem case0054 : minimalVertices [0,1,0] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [[],[false],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [[false],[true,false],[true,true]] := by decide
#print axioms case0054
theorem case0055 : minimalVertices [25] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [] ∧ terminals [25] (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms case0055
theorem case0056 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [] ∧ terminals [] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms case0056
theorem case0057 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [[],[false],[true],[true,true]] ∧ terminals [0] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [[false],[true,true]] := by decide
#print axioms case0057
theorem case0058 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [[true,false]] ∧ terminals [1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [[true,false]] := by decide
#print axioms case0058
theorem case0059 : minimalVertices [0,1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [[],[false],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [[false],[true,false],[true,true]] := by decide
#print axioms case0059
theorem case0060 : minimalVertices [0,0] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [[],[false],[true],[true,true]] ∧ terminals [0,0] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [[false],[true,true]] := by decide
#print axioms case0060
theorem case0061 : minimalVertices [0,1,0] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [[],[false],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [[false],[true,false],[true,true]] := by decide
#print axioms case0061
theorem case0062 : minimalVertices [25] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [] ∧ terminals [25] (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms case0062
theorem case0063 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [] ∧ terminals [] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms case0063
theorem case0064 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [[false]] ∧ terminals [0] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [[false]] := by decide
#print axioms case0064
theorem case0065 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [[true],[true,false],[true,true]] ∧ terminals [1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [[true,false],[true,true]] := by decide
#print axioms case0065
theorem case0066 : minimalVertices [0,1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [[],[false],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [[false],[true,false],[true,true]] := by decide
#print axioms case0066
theorem case0067 : minimalVertices [0,0] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [[false]] ∧ terminals [0,0] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [[false]] := by decide
#print axioms case0067
theorem case0068 : minimalVertices [0,1,0] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [[],[false],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [[false],[true,false],[true,true]] := by decide
#print axioms case0068
theorem case0069 : minimalVertices [25] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [] ∧ terminals [25] (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms case0069
theorem case0070 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [] ∧ terminals [] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms case0070
theorem case0071 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [[true],[true,false],[true,true]] ∧ terminals [0] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [[true,false],[true,true]] := by decide
#print axioms case0071
theorem case0072 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [[false]] ∧ terminals [1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [[false]] := by decide
#print axioms case0072
theorem case0073 : minimalVertices [0,1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [[],[false],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [[false],[true,false],[true,true]] := by decide
#print axioms case0073
theorem case0074 : minimalVertices [0,0] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [[true],[true,false],[true,true]] ∧ terminals [0,0] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [[true,false],[true,true]] := by decide
#print axioms case0074
theorem case0075 : minimalVertices [0,1,0] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [[],[false],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [[false],[true,false],[true,true]] := by decide
#print axioms case0075
theorem case0076 : minimalVertices [25] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [] ∧ terminals [25] (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms case0076
theorem case0077 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [] ∧ terminals [] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms case0077
theorem case0078 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [[true,false]] ∧ terminals [0] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [[true,false]] := by decide
#print axioms case0078
theorem case0079 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [[],[false],[true],[true,true]] ∧ terminals [1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [[false],[true,true]] := by decide
#print axioms case0079
theorem case0080 : minimalVertices [0,1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [[],[false],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [[false],[true,false],[true,true]] := by decide
#print axioms case0080
theorem case0081 : minimalVertices [0,0] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [[true,false]] ∧ terminals [0,0] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [[true,false]] := by decide
#print axioms case0081
theorem case0082 : minimalVertices [0,1,0] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [[],[false],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [[false],[true,false],[true,true]] := by decide
#print axioms case0082
theorem case0083 : minimalVertices [25] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [] ∧ terminals [25] (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms case0083
theorem case0084 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [] ∧ terminals [] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms case0084
theorem case0085 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [[true,true]] ∧ terminals [0] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [[true,true]] := by decide
#print axioms case0085
theorem case0086 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [[],[false],[true],[true,false]] ∧ terminals [1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [[false],[true,false]] := by decide
#print axioms case0086
theorem case0087 : minimalVertices [0,1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [[],[false],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [[false],[true,false],[true,true]] := by decide
#print axioms case0087
theorem case0088 : minimalVertices [0,0] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [[true,true]] ∧ terminals [0,0] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [[true,true]] := by decide
#print axioms case0088
theorem case0089 : minimalVertices [0,1,0] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [[],[false],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [[false],[true,false],[true,true]] := by decide
#print axioms case0089
theorem case0090 : minimalVertices [25] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [] ∧ terminals [25] (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms case0090
theorem case0091 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [] ∧ terminals [] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms case0091
theorem case0092 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [] ∧ terminals [0] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms case0092
theorem case0093 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [[],[false],[true],[true,false],[true,true]] ∧ terminals [1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [[false],[true,false],[true,true]] := by decide
#print axioms case0093
theorem case0094 : minimalVertices [0,1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [[],[false],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [[false],[true,false],[true,true]] := by decide
#print axioms case0094
theorem case0095 : minimalVertices [0,0] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [] ∧ terminals [0,0] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms case0095
theorem case0096 : minimalVertices [0,1,0] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [[],[false],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [[false],[true,false],[true,true]] := by decide
#print axioms case0096
theorem case0097 : minimalVertices [25] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [] ∧ terminals [25] (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms case0097
theorem case0098 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [] ∧ terminals [] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms case0098
theorem case0099 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,true],[true]] ∧ terminals [0] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [[false,false],[false,true],[true]] := by decide
#print axioms case0099
theorem case0100 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [] ∧ terminals [1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms case0100
theorem case0101 : minimalVertices [0,1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [[false,false],[false,true],[true]] := by decide
#print axioms case0101
theorem case0102 : minimalVertices [0,0] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,true],[true]] ∧ terminals [0,0] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [[false,false],[false,true],[true]] := by decide
#print axioms case0102
theorem case0103 : minimalVertices [0,1,0] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [[false,false],[false,true],[true]] := by decide
#print axioms case0103
theorem case0104 : minimalVertices [25] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [] ∧ terminals [25] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms case0104
theorem case0105 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [] ∧ terminals [] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms case0105
theorem case0106 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [[false],[false,false],[false,true]] ∧ terminals [0] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [[false,false],[false,true]] := by decide
#print axioms case0106
theorem case0107 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [[true]] ∧ terminals [1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [[true]] := by decide
#print axioms case0107
theorem case0108 : minimalVertices [0,1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [[false,false],[false,true],[true]] := by decide
#print axioms case0108
theorem case0109 : minimalVertices [0,0] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [[false],[false,false],[false,true]] ∧ terminals [0,0] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [[false,false],[false,true]] := by decide
#print axioms case0109
theorem case0110 : minimalVertices [0,1,0] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [[false,false],[false,true],[true]] := by decide
#print axioms case0110
theorem case0111 : minimalVertices [25] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [] ∧ terminals [25] (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms case0111
theorem case0112 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [] ∧ terminals [] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms case0112
theorem case0113 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[true]] ∧ terminals [0] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [[false,false],[true]] := by decide
#print axioms case0113
theorem case0114 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [[false,true]] ∧ terminals [1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [[false,true]] := by decide
#print axioms case0114
theorem case0115 : minimalVertices [0,1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [[false,false],[false,true],[true]] := by decide
#print axioms case0115
theorem case0116 : minimalVertices [0,0] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[true]] ∧ terminals [0,0] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [[false,false],[true]] := by decide
#print axioms case0116
theorem case0117 : minimalVertices [0,1,0] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [[false,false],[false,true],[true]] := by decide
#print axioms case0117
theorem case0118 : minimalVertices [25] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [] ∧ terminals [25] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms case0118
theorem case0119 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [] ∧ terminals [] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms case0119
theorem case0120 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [[false,false]] ∧ terminals [0] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [[false,false]] := by decide
#print axioms case0120
theorem case0121 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [[],[false],[false,true],[true]] ∧ terminals [1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [[false,true],[true]] := by decide
#print axioms case0121
theorem case0122 : minimalVertices [0,1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [[false,false],[false,true],[true]] := by decide
#print axioms case0122
theorem case0123 : minimalVertices [0,0] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [[false,false]] ∧ terminals [0,0] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [[false,false]] := by decide
#print axioms case0123
theorem case0124 : minimalVertices [0,1,0] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [[false,false],[false,true],[true]] := by decide
#print axioms case0124
theorem case0125 : minimalVertices [25] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [] ∧ terminals [25] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms case0125
theorem case0126 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [] ∧ terminals [] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms case0126
theorem case0127 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [[],[false],[false,true],[true]] ∧ terminals [0] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [[false,true],[true]] := by decide
#print axioms case0127
theorem case0128 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [[false,false]] ∧ terminals [1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [[false,false]] := by decide
#print axioms case0128
theorem case0129 : minimalVertices [0,1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [[false,false],[false,true],[true]] := by decide
#print axioms case0129
theorem case0130 : minimalVertices [0,0] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [[],[false],[false,true],[true]] ∧ terminals [0,0] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [[false,true],[true]] := by decide
#print axioms case0130
theorem case0131 : minimalVertices [0,1,0] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [[false,false],[false,true],[true]] := by decide
#print axioms case0131
theorem case0132 : minimalVertices [25] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [] ∧ terminals [25] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms case0132
theorem case0133 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [] ∧ terminals [] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms case0133
theorem case0134 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [[false,true]] ∧ terminals [0] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [[false,true]] := by decide
#print axioms case0134
theorem case0135 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[true]] ∧ terminals [1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [[false,false],[true]] := by decide
#print axioms case0135
theorem case0136 : minimalVertices [0,1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [[false,false],[false,true],[true]] := by decide
#print axioms case0136
theorem case0137 : minimalVertices [0,0] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [[false,true]] ∧ terminals [0,0] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [[false,true]] := by decide
#print axioms case0137
theorem case0138 : minimalVertices [0,1,0] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [[false,false],[false,true],[true]] := by decide
#print axioms case0138
theorem case0139 : minimalVertices [25] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [] ∧ terminals [25] (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms case0139
theorem case0140 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [] ∧ terminals [] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms case0140
theorem case0141 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [[true]] ∧ terminals [0] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [[true]] := by decide
#print axioms case0141
theorem case0142 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [[false],[false,false],[false,true]] ∧ terminals [1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [[false,false],[false,true]] := by decide
#print axioms case0142
theorem case0143 : minimalVertices [0,1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [[false,false],[false,true],[true]] := by decide
#print axioms case0143
theorem case0144 : minimalVertices [0,0] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [[true]] ∧ terminals [0,0] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [[true]] := by decide
#print axioms case0144
theorem case0145 : minimalVertices [0,1,0] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [[false,false],[false,true],[true]] := by decide
#print axioms case0145
theorem case0146 : minimalVertices [25] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [] ∧ terminals [25] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms case0146
theorem case0147 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [] ∧ terminals [] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms case0147
theorem case0148 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [] ∧ terminals [0] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms case0148
theorem case0149 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,true],[true]] ∧ terminals [1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [[false,false],[false,true],[true]] := by decide
#print axioms case0149
theorem case0150 : minimalVertices [0,1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [[false,false],[false,true],[true]] := by decide
#print axioms case0150
theorem case0151 : minimalVertices [0,0] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [] ∧ terminals [0,0] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms case0151
theorem case0152 : minimalVertices [0,1,0] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [[false,false],[false,true],[true]] := by decide
#print axioms case0152
theorem case0153 : minimalVertices [25] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [] ∧ terminals [25] (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms case0153
theorem case0154 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [] ∧ terminals [] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
#print axioms case0154
theorem case0155 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0155
theorem case0156 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [] ∧ terminals [1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
#print axioms case0156
theorem case0157 : minimalVertices [0,1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0157
theorem case0158 : minimalVertices [0,0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0158
theorem case0159 : minimalVertices [0,1,0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1,0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0159
theorem case0160 : minimalVertices [25] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [] ∧ terminals [25] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
#print axioms case0160
theorem case0161 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [] ∧ terminals [] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
#print axioms case0161
theorem case0162 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false]] ∧ terminals [0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[false],[true,false],[true,true,false]] := by decide
#print axioms case0162
theorem case0163 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[true,true,true]] ∧ terminals [1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[true,true,true]] := by decide
#print axioms case0163
theorem case0164 : minimalVertices [0,1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0164
theorem case0165 : minimalVertices [0,0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false]] ∧ terminals [0,0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[false],[true,false],[true,true,false]] := by decide
#print axioms case0165
theorem case0166 : minimalVertices [0,1,0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1,0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0166
theorem case0167 : minimalVertices [25] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [] ∧ terminals [25] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
#print axioms case0167
theorem case0168 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [] ∧ terminals [] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
#print axioms case0168
theorem case0169 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,true]] ∧ terminals [0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[false],[true,false],[true,true,true]] := by decide
#print axioms case0169
theorem case0170 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[true,true,false]] ∧ terminals [1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[true,true,false]] := by decide
#print axioms case0170
theorem case0171 : minimalVertices [0,1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0171
theorem case0172 : minimalVertices [0,0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,true]] ∧ terminals [0,0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[false],[true,false],[true,true,true]] := by decide
#print axioms case0172
theorem case0173 : minimalVertices [0,1,0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1,0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0173
theorem case0174 : minimalVertices [25] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [] ∧ terminals [25] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
#print axioms case0174
theorem case0175 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [] ∧ terminals [] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
#print axioms case0175
theorem case0176 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false]] ∧ terminals [0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[false],[true,false]] := by decide
#print axioms case0176
theorem case0177 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[true,true],[true,true,false],[true,true,true]] ∧ terminals [1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[true,true,false],[true,true,true]] := by decide
#print axioms case0177
theorem case0178 : minimalVertices [0,1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0178
theorem case0179 : minimalVertices [0,0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false]] ∧ terminals [0,0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[false],[true,false]] := by decide
#print axioms case0179
theorem case0180 : minimalVertices [0,1,0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1,0] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0180
theorem case0181 : minimalVertices [25] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [] ∧ terminals [25] (.node (.leaf 0) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
#print axioms case0181
theorem case0182 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [] ∧ terminals [] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
#print axioms case0182
theorem case0183 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[false],[true,true,false],[true,true,true]] := by decide
#print axioms case0183
theorem case0184 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[true,false]] ∧ terminals [1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[true,false]] := by decide
#print axioms case0184
theorem case0185 : minimalVertices [0,1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0185
theorem case0186 : minimalVertices [0,0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[false],[true,true,false],[true,true,true]] := by decide
#print axioms case0186
theorem case0187 : minimalVertices [0,1,0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1,0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0187
theorem case0188 : minimalVertices [25] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [] ∧ terminals [25] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
#print axioms case0188
theorem case0189 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [] ∧ terminals [] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
#print axioms case0189
theorem case0190 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,true],[true,true,false]] ∧ terminals [0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[false],[true,true,false]] := by decide
#print axioms case0190
theorem case0191 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[true],[true,false],[true,true],[true,true,true]] ∧ terminals [1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[true,false],[true,true,true]] := by decide
#print axioms case0191
theorem case0192 : minimalVertices [0,1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0192
theorem case0193 : minimalVertices [0,0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,true],[true,true,false]] ∧ terminals [0,0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[false],[true,true,false]] := by decide
#print axioms case0193
theorem case0194 : minimalVertices [0,1,0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1,0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0194
theorem case0195 : minimalVertices [25] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [] ∧ terminals [25] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
#print axioms case0195
theorem case0196 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [] ∧ terminals [] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
#print axioms case0196
theorem case0197 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,true],[true,true,true]] ∧ terminals [0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[false],[true,true,true]] := by decide
#print axioms case0197
theorem case0198 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[true],[true,false],[true,true],[true,true,false]] ∧ terminals [1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[true,false],[true,true,false]] := by decide
#print axioms case0198
theorem case0199 : minimalVertices [0,1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0199
theorem case0200 : minimalVertices [0,0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,true],[true,true,true]] ∧ terminals [0,0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[false],[true,true,true]] := by decide
#print axioms case0200
theorem case0201 : minimalVertices [0,1,0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1,0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0201
theorem case0202 : minimalVertices [25] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [] ∧ terminals [25] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
#print axioms case0202
theorem case0203 : minimalVertices [] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] ∧ terminals [] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
#print axioms case0203
theorem case0204 : minimalVertices [0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[false]] ∧ terminals [0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[false]] := by decide
#print axioms case0204
theorem case0205 : minimalVertices [1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0205
theorem case0206 : minimalVertices [0,1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0206
theorem case0207 : minimalVertices [0,0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[false]] ∧ terminals [0,0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[false]] := by decide
#print axioms case0207
theorem case0208 : minimalVertices [0,1,0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1,0] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0208
theorem case0209 : minimalVertices [25] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] ∧ terminals [25] (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
#print axioms case0209
theorem case0210 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [] ∧ terminals [] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
#print axioms case0210
theorem case0211 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0211
theorem case0212 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[false]] ∧ terminals [1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[false]] := by decide
#print axioms case0212
theorem case0213 : minimalVertices [0,1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0213
theorem case0214 : minimalVertices [0,0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0214
theorem case0215 : minimalVertices [0,1,0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1,0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0215
theorem case0216 : minimalVertices [25] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [] ∧ terminals [25] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
#print axioms case0216
theorem case0217 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [] ∧ terminals [] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
#print axioms case0217
theorem case0218 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[true],[true,false],[true,true],[true,true,false]] ∧ terminals [0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[true,false],[true,true,false]] := by decide
#print axioms case0218
theorem case0219 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,true],[true,true,true]] ∧ terminals [1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[false],[true,true,true]] := by decide
#print axioms case0219
theorem case0220 : minimalVertices [0,1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0220
theorem case0221 : minimalVertices [0,0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[true],[true,false],[true,true],[true,true,false]] ∧ terminals [0,0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[true,false],[true,true,false]] := by decide
#print axioms case0221
theorem case0222 : minimalVertices [0,1,0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1,0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0222
theorem case0223 : minimalVertices [25] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [] ∧ terminals [25] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
#print axioms case0223
theorem case0224 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [] ∧ terminals [] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
#print axioms case0224
theorem case0225 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[true],[true,false],[true,true],[true,true,true]] ∧ terminals [0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[true,false],[true,true,true]] := by decide
#print axioms case0225
theorem case0226 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,true],[true,true,false]] ∧ terminals [1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[false],[true,true,false]] := by decide
#print axioms case0226
theorem case0227 : minimalVertices [0,1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0227
theorem case0228 : minimalVertices [0,0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[true],[true,false],[true,true],[true,true,true]] ∧ terminals [0,0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[true,false],[true,true,true]] := by decide
#print axioms case0228
theorem case0229 : minimalVertices [0,1,0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1,0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0229
theorem case0230 : minimalVertices [25] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [] ∧ terminals [25] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
#print axioms case0230
theorem case0231 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [] ∧ terminals [] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
#print axioms case0231
theorem case0232 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[true,false]] ∧ terminals [0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[true,false]] := by decide
#print axioms case0232
theorem case0233 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,true],[true,true,false],[true,true,true]] ∧ terminals [1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[false],[true,true,false],[true,true,true]] := by decide
#print axioms case0233
theorem case0234 : minimalVertices [0,1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0234
theorem case0235 : minimalVertices [0,0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[true,false]] ∧ terminals [0,0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[true,false]] := by decide
#print axioms case0235
theorem case0236 : minimalVertices [0,1,0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1,0] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0236
theorem case0237 : minimalVertices [25] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [] ∧ terminals [25] (.node (.leaf 1) (.node (.leaf 0) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
#print axioms case0237
theorem case0238 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [] ∧ terminals [] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
#print axioms case0238
theorem case0239 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[true,true],[true,true,false],[true,true,true]] ∧ terminals [0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[true,true,false],[true,true,true]] := by decide
#print axioms case0239
theorem case0240 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false]] ∧ terminals [1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[false],[true,false]] := by decide
#print axioms case0240
theorem case0241 : minimalVertices [0,1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0241
theorem case0242 : minimalVertices [0,0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[true,true,false],[true,true,true]] := by decide
#print axioms case0242
theorem case0243 : minimalVertices [0,1,0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1,0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0243
theorem case0244 : minimalVertices [25] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [] ∧ terminals [25] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 0)))) = [] := by decide
#print axioms case0244
theorem case0245 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [] ∧ terminals [] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
#print axioms case0245
theorem case0246 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[true,true,false]] ∧ terminals [0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[true,true,false]] := by decide
#print axioms case0246
theorem case0247 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,true]] ∧ terminals [1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[false],[true,false],[true,true,true]] := by decide
#print axioms case0247
theorem case0248 : minimalVertices [0,1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0248
theorem case0249 : minimalVertices [0,0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[true,true,false]] ∧ terminals [0,0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[true,true,false]] := by decide
#print axioms case0249
theorem case0250 : minimalVertices [0,1,0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1,0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0250
theorem case0251 : minimalVertices [25] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [] ∧ terminals [25] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 0) (.leaf 1)))) = [] := by decide
#print axioms case0251
theorem case0252 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [] ∧ terminals [] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
#print axioms case0252
theorem case0253 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[true,true,true]] ∧ terminals [0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[true,true,true]] := by decide
#print axioms case0253
theorem case0254 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false]] ∧ terminals [1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[false],[true,false],[true,true,false]] := by decide
#print axioms case0254
theorem case0255 : minimalVertices [0,1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0255
theorem case0256 : minimalVertices [0,0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[true,true,true]] ∧ terminals [0,0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[true,true,true]] := by decide
#print axioms case0256
theorem case0257 : minimalVertices [0,1,0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1,0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0257
theorem case0258 : minimalVertices [25] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [] ∧ terminals [25] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 0)))) = [] := by decide
#print axioms case0258
theorem case0259 : minimalVertices [] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] ∧ terminals [] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
#print axioms case0259
theorem case0260 : minimalVertices [0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] ∧ terminals [0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
#print axioms case0260
theorem case0261 : minimalVertices [1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0261
theorem case0262 : minimalVertices [0,1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0262
theorem case0263 : minimalVertices [0,0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] ∧ terminals [0,0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
#print axioms case0263
theorem case0264 : minimalVertices [0,1,0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[],[false],[true],[true,false],[true,true],[true,true,false],[true,true,true]] ∧ terminals [0,1,0] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [[false],[true,false],[true,true,false],[true,true,true]] := by decide
#print axioms case0264
theorem case0265 : minimalVertices [25] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] ∧ terminals [25] (.node (.leaf 1) (.node (.leaf 1) (.node (.leaf 1) (.leaf 1)))) = [] := by decide
#print axioms case0265
theorem case0266 : minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [] ∧ terminals [] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [] := by decide
#print axioms case0266
theorem case0267 : minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0267
theorem case0268 : minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [] ∧ terminals [1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [] := by decide
#print axioms case0268
theorem case0269 : minimalVertices [0,1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0269
theorem case0270 : minimalVertices [0,0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0270
theorem case0271 : minimalVertices [0,1,0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0271
theorem case0272 : minimalVertices [25] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [] ∧ terminals [25] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [] := by decide
#print axioms case0272
theorem case0273 : minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [] ∧ terminals [] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [] := by decide
#print axioms case0273
theorem case0274 : minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true]] ∧ terminals [0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[false],[true,false,false],[true,false,true]] := by decide
#print axioms case0274
theorem case0275 : minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[true,true]] ∧ terminals [1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[true,true]] := by decide
#print axioms case0275
theorem case0276 : minimalVertices [0,1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0276
theorem case0277 : minimalVertices [0,0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true]] ∧ terminals [0,0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[false],[true,false,false],[true,false,true]] := by decide
#print axioms case0277
theorem case0278 : minimalVertices [0,1,0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0278
theorem case0279 : minimalVertices [25] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [] ∧ terminals [25] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [] := by decide
#print axioms case0279
theorem case0280 : minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [] ∧ terminals [] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [] := by decide
#print axioms case0280
theorem case0281 : minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,true]] ∧ terminals [0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[false],[true,false,false],[true,true]] := by decide
#print axioms case0281
theorem case0282 : minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[true,false,true]] ∧ terminals [1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[true,false,true]] := by decide
#print axioms case0282
theorem case0283 : minimalVertices [0,1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0283
theorem case0284 : minimalVertices [0,0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,true]] ∧ terminals [0,0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[false],[true,false,false],[true,true]] := by decide
#print axioms case0284
theorem case0285 : minimalVertices [0,1,0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0285
theorem case0286 : minimalVertices [25] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [] ∧ terminals [25] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [] := by decide
#print axioms case0286
theorem case0287 : minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [] ∧ terminals [] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [] := by decide
#print axioms case0287
theorem case0288 : minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false]] ∧ terminals [0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[false],[true,false,false]] := by decide
#print axioms case0288
theorem case0289 : minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[true],[true,false],[true,false,true],[true,true]] ∧ terminals [1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[true,false,true],[true,true]] := by decide
#print axioms case0289
theorem case0290 : minimalVertices [0,1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0290
theorem case0291 : minimalVertices [0,0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false]] ∧ terminals [0,0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[false],[true,false,false]] := by decide
#print axioms case0291
theorem case0292 : minimalVertices [0,1,0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0292
theorem case0293 : minimalVertices [25] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [] ∧ terminals [25] (.node (.leaf 0) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [] := by decide
#print axioms case0293
theorem case0294 : minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [] ∧ terminals [] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [] := by decide
#print axioms case0294
theorem case0295 : minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,true],[true,true]] ∧ terminals [0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[false],[true,false,true],[true,true]] := by decide
#print axioms case0295
theorem case0296 : minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[true,false,false]] ∧ terminals [1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[true,false,false]] := by decide
#print axioms case0296
theorem case0297 : minimalVertices [0,1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0297
theorem case0298 : minimalVertices [0,0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,true],[true,true]] ∧ terminals [0,0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[false],[true,false,true],[true,true]] := by decide
#print axioms case0298
theorem case0299 : minimalVertices [0,1,0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0299
theorem case0300 : minimalVertices [25] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [] ∧ terminals [25] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [] := by decide
#print axioms case0300
theorem case0301 : minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [] ∧ terminals [] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [] := by decide
#print axioms case0301
theorem case0302 : minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,true]] ∧ terminals [0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[false],[true,false,true]] := by decide
#print axioms case0302
theorem case0303 : minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[true],[true,false],[true,false,false],[true,true]] ∧ terminals [1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[true,false,false],[true,true]] := by decide
#print axioms case0303
theorem case0304 : minimalVertices [0,1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0304
theorem case0305 : minimalVertices [0,0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,true]] ∧ terminals [0,0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[false],[true,false,true]] := by decide
#print axioms case0305
theorem case0306 : minimalVertices [0,1,0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0306
theorem case0307 : minimalVertices [25] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [] ∧ terminals [25] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [] := by decide
#print axioms case0307
theorem case0308 : minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [] ∧ terminals [] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [] := by decide
#print axioms case0308
theorem case0309 : minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,true]] ∧ terminals [0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[false],[true,true]] := by decide
#print axioms case0309
theorem case0310 : minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[true,false],[true,false,false],[true,false,true]] ∧ terminals [1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[true,false,false],[true,false,true]] := by decide
#print axioms case0310
theorem case0311 : minimalVertices [0,1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0311
theorem case0312 : minimalVertices [0,0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,true]] ∧ terminals [0,0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[false],[true,true]] := by decide
#print axioms case0312
theorem case0313 : minimalVertices [0,1,0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0313
theorem case0314 : minimalVertices [25] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [] ∧ terminals [25] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [] := by decide
#print axioms case0314
theorem case0315 : minimalVertices [] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] ∧ terminals [] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] := by decide
#print axioms case0315
theorem case0316 : minimalVertices [0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[false]] ∧ terminals [0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[false]] := by decide
#print axioms case0316
theorem case0317 : minimalVertices [1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0317
theorem case0318 : minimalVertices [0,1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0318
theorem case0319 : minimalVertices [0,0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[false]] ∧ terminals [0,0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[false]] := by decide
#print axioms case0319
theorem case0320 : minimalVertices [0,1,0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0320
theorem case0321 : minimalVertices [25] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] ∧ terminals [25] (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] := by decide
#print axioms case0321
theorem case0322 : minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [] ∧ terminals [] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [] := by decide
#print axioms case0322
theorem case0323 : minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0323
theorem case0324 : minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[false]] ∧ terminals [1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[false]] := by decide
#print axioms case0324
theorem case0325 : minimalVertices [0,1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0325
theorem case0326 : minimalVertices [0,0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0326
theorem case0327 : minimalVertices [0,1,0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0327
theorem case0328 : minimalVertices [25] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [] ∧ terminals [25] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0))) = [] := by decide
#print axioms case0328
theorem case0329 : minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [] ∧ terminals [] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [] := by decide
#print axioms case0329
theorem case0330 : minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[true,false],[true,false,false],[true,false,true]] ∧ terminals [0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[true,false,false],[true,false,true]] := by decide
#print axioms case0330
theorem case0331 : minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,true]] ∧ terminals [1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[false],[true,true]] := by decide
#print axioms case0331
theorem case0332 : minimalVertices [0,1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0332
theorem case0333 : minimalVertices [0,0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[true,false],[true,false,false],[true,false,true]] ∧ terminals [0,0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[true,false,false],[true,false,true]] := by decide
#print axioms case0333
theorem case0334 : minimalVertices [0,1,0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0334
theorem case0335 : minimalVertices [25] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [] ∧ terminals [25] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1))) = [] := by decide
#print axioms case0335
theorem case0336 : minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [] ∧ terminals [] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [] := by decide
#print axioms case0336
theorem case0337 : minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[true],[true,false],[true,false,false],[true,true]] ∧ terminals [0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[true,false,false],[true,true]] := by decide
#print axioms case0337
theorem case0338 : minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,true]] ∧ terminals [1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[false],[true,false,true]] := by decide
#print axioms case0338
theorem case0339 : minimalVertices [0,1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0339
theorem case0340 : minimalVertices [0,0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[true],[true,false],[true,false,false],[true,true]] ∧ terminals [0,0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[true,false,false],[true,true]] := by decide
#print axioms case0340
theorem case0341 : minimalVertices [0,1,0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0341
theorem case0342 : minimalVertices [25] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [] ∧ terminals [25] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0))) = [] := by decide
#print axioms case0342
theorem case0343 : minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [] ∧ terminals [] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [] := by decide
#print axioms case0343
theorem case0344 : minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[true,false,false]] ∧ terminals [0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[true,false,false]] := by decide
#print axioms case0344
theorem case0345 : minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,true],[true,true]] ∧ terminals [1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[false],[true,false,true],[true,true]] := by decide
#print axioms case0345
theorem case0346 : minimalVertices [0,1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0346
theorem case0347 : minimalVertices [0,0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[true,false,false]] ∧ terminals [0,0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[true,false,false]] := by decide
#print axioms case0347
theorem case0348 : minimalVertices [0,1,0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0348
theorem case0349 : minimalVertices [25] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [] ∧ terminals [25] (.node (.leaf 1) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1))) = [] := by decide
#print axioms case0349
theorem case0350 : minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [] ∧ terminals [] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [] := by decide
#print axioms case0350
theorem case0351 : minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[true],[true,false],[true,false,true],[true,true]] ∧ terminals [0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[true,false,true],[true,true]] := by decide
#print axioms case0351
theorem case0352 : minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false]] ∧ terminals [1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[false],[true,false,false]] := by decide
#print axioms case0352
theorem case0353 : minimalVertices [0,1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0353
theorem case0354 : minimalVertices [0,0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[true],[true,false],[true,false,true],[true,true]] ∧ terminals [0,0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[true,false,true],[true,true]] := by decide
#print axioms case0354
theorem case0355 : minimalVertices [0,1,0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0355
theorem case0356 : minimalVertices [25] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [] ∧ terminals [25] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0))) = [] := by decide
#print axioms case0356
theorem case0357 : minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [] ∧ terminals [] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [] := by decide
#print axioms case0357
theorem case0358 : minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[true,false,true]] ∧ terminals [0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[true,false,true]] := by decide
#print axioms case0358
theorem case0359 : minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,true]] ∧ terminals [1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[false],[true,false,false],[true,true]] := by decide
#print axioms case0359
theorem case0360 : minimalVertices [0,1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0360
theorem case0361 : minimalVertices [0,0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[true,false,true]] ∧ terminals [0,0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[true,false,true]] := by decide
#print axioms case0361
theorem case0362 : minimalVertices [0,1,0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0362
theorem case0363 : minimalVertices [25] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [] ∧ terminals [25] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1))) = [] := by decide
#print axioms case0363
theorem case0364 : minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [] ∧ terminals [] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [] := by decide
#print axioms case0364
theorem case0365 : minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[true,true]] ∧ terminals [0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[true,true]] := by decide
#print axioms case0365
theorem case0366 : minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true]] ∧ terminals [1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[false],[true,false,false],[true,false,true]] := by decide
#print axioms case0366
theorem case0367 : minimalVertices [0,1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0367
theorem case0368 : minimalVertices [0,0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[true,true]] ∧ terminals [0,0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[true,true]] := by decide
#print axioms case0368
theorem case0369 : minimalVertices [0,1,0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0369
theorem case0370 : minimalVertices [25] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [] ∧ terminals [25] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0))) = [] := by decide
#print axioms case0370
theorem case0371 : minimalVertices [] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] ∧ terminals [] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] := by decide
#print axioms case0371
theorem case0372 : minimalVertices [0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] ∧ terminals [0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] := by decide
#print axioms case0372
theorem case0373 : minimalVertices [1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0373
theorem case0374 : minimalVertices [0,1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0374
theorem case0375 : minimalVertices [0,0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] ∧ terminals [0,0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] := by decide
#print axioms case0375
theorem case0376 : minimalVertices [0,1,0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[],[false],[true],[true,false],[true,false,false],[true,false,true],[true,true]] ∧ terminals [0,1,0] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [[false],[true,false,false],[true,false,true],[true,true]] := by decide
#print axioms case0376
theorem case0377 : minimalVertices [25] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] ∧ terminals [25] (.node (.leaf 1) (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1))) = [] := by decide
#print axioms case0377
theorem case0378 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [] ∧ terminals [] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms case0378
theorem case0379 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0379
theorem case0380 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [] ∧ terminals [1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms case0380
theorem case0381 : minimalVertices [0,1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0381
theorem case0382 : minimalVertices [0,0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0382
theorem case0383 : minimalVertices [0,1,0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0383
theorem case0384 : minimalVertices [25] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [] ∧ terminals [25] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms case0384
theorem case0385 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [] ∧ terminals [] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms case0385
theorem case0386 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false]] ∧ terminals [0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[false,false],[false,true],[true,false]] := by decide
#print axioms case0386
theorem case0387 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[true,true]] ∧ terminals [1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[true,true]] := by decide
#print axioms case0387
theorem case0388 : minimalVertices [0,1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0388
theorem case0389 : minimalVertices [0,0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false]] ∧ terminals [0,0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[false,false],[false,true],[true,false]] := by decide
#print axioms case0389
theorem case0390 : minimalVertices [0,1,0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0390
theorem case0391 : minimalVertices [25] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [] ∧ terminals [25] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms case0391
theorem case0392 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [] ∧ terminals [] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms case0392
theorem case0393 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,true]] ∧ terminals [0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[false,false],[false,true],[true,true]] := by decide
#print axioms case0393
theorem case0394 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[true,false]] ∧ terminals [1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[true,false]] := by decide
#print axioms case0394
theorem case0395 : minimalVertices [0,1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0395
theorem case0396 : minimalVertices [0,0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,true]] ∧ terminals [0,0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[false,false],[false,true],[true,true]] := by decide
#print axioms case0396
theorem case0397 : minimalVertices [0,1,0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0397
theorem case0398 : minimalVertices [25] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [] ∧ terminals [25] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms case0398
theorem case0399 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [] ∧ terminals [] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms case0399
theorem case0400 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[false],[false,false],[false,true]] ∧ terminals [0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[false,false],[false,true]] := by decide
#print axioms case0400
theorem case0401 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[true],[true,false],[true,true]] ∧ terminals [1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[true,false],[true,true]] := by decide
#print axioms case0401
theorem case0402 : minimalVertices [0,1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0402
theorem case0403 : minimalVertices [0,0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[false],[false,false],[false,true]] ∧ terminals [0,0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[false,false],[false,true]] := by decide
#print axioms case0403
theorem case0404 : minimalVertices [0,1,0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0404
theorem case0405 : minimalVertices [25] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [] ∧ terminals [25] (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms case0405
theorem case0406 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [] ∧ terminals [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms case0406
theorem case0407 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[true],[true,false],[true,true]] ∧ terminals [0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[false,false],[true,false],[true,true]] := by decide
#print axioms case0407
theorem case0408 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[false,true]] ∧ terminals [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[false,true]] := by decide
#print axioms case0408
theorem case0409 : minimalVertices [0,1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0409
theorem case0410 : minimalVertices [0,0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[true],[true,false],[true,true]] ∧ terminals [0,0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[false,false],[true,false],[true,true]] := by decide
#print axioms case0410
theorem case0411 : minimalVertices [0,1,0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0411
theorem case0412 : minimalVertices [25] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [] ∧ terminals [25] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms case0412
theorem case0413 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [] ∧ terminals [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms case0413
theorem case0414 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[true],[true,false]] ∧ terminals [0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[false,false],[true,false]] := by decide
#print axioms case0414
theorem case0415 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,true],[true],[true,true]] ∧ terminals [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[false,true],[true,true]] := by decide
#print axioms case0415
theorem case0416 : minimalVertices [0,1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0416
theorem case0417 : minimalVertices [0,0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[true],[true,false]] ∧ terminals [0,0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[false,false],[true,false]] := by decide
#print axioms case0417
theorem case0418 : minimalVertices [0,1,0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0418
theorem case0419 : minimalVertices [25] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [] ∧ terminals [25] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms case0419
theorem case0420 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [] ∧ terminals [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms case0420
theorem case0421 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[true],[true,true]] ∧ terminals [0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[false,false],[true,true]] := by decide
#print axioms case0421
theorem case0422 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,true],[true],[true,false]] ∧ terminals [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[false,true],[true,false]] := by decide
#print axioms case0422
theorem case0423 : minimalVertices [0,1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0423
theorem case0424 : minimalVertices [0,0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[true],[true,true]] ∧ terminals [0,0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[false,false],[true,true]] := by decide
#print axioms case0424
theorem case0425 : minimalVertices [0,1,0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0425
theorem case0426 : minimalVertices [25] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [] ∧ terminals [25] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms case0426
theorem case0427 : minimalVertices [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] ∧ terminals [] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms case0427
theorem case0428 : minimalVertices [0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[false,false]] ∧ terminals [0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[false,false]] := by decide
#print axioms case0428
theorem case0429 : minimalVertices [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,true],[true],[true,false],[true,true]] ∧ terminals [1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[false,true],[true,false],[true,true]] := by decide
#print axioms case0429
theorem case0430 : minimalVertices [0,1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0430
theorem case0431 : minimalVertices [0,0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[false,false]] ∧ terminals [0,0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[false,false]] := by decide
#print axioms case0431
theorem case0432 : minimalVertices [0,1,0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0432
theorem case0433 : minimalVertices [25] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] ∧ terminals [25] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms case0433
theorem case0434 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [] ∧ terminals [] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms case0434
theorem case0435 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[false,true],[true,false],[true,true]] := by decide
#print axioms case0435
theorem case0436 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[false,false]] ∧ terminals [1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[false,false]] := by decide
#print axioms case0436
theorem case0437 : minimalVertices [0,1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0437
theorem case0438 : minimalVertices [0,0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[false,true],[true,false],[true,true]] := by decide
#print axioms case0438
theorem case0439 : minimalVertices [0,1,0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0439
theorem case0440 : minimalVertices [25] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [] ∧ terminals [25] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms case0440
theorem case0441 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [] ∧ terminals [] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms case0441
theorem case0442 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,true],[true],[true,false]] ∧ terminals [0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[false,true],[true,false]] := by decide
#print axioms case0442
theorem case0443 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[true],[true,true]] ∧ terminals [1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[false,false],[true,true]] := by decide
#print axioms case0443
theorem case0444 : minimalVertices [0,1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0444
theorem case0445 : minimalVertices [0,0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,true],[true],[true,false]] ∧ terminals [0,0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[false,true],[true,false]] := by decide
#print axioms case0445
theorem case0446 : minimalVertices [0,1,0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0446
theorem case0447 : minimalVertices [25] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [] ∧ terminals [25] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms case0447
theorem case0448 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [] ∧ terminals [] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms case0448
theorem case0449 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,true],[true],[true,true]] ∧ terminals [0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[false,true],[true,true]] := by decide
#print axioms case0449
theorem case0450 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[true],[true,false]] ∧ terminals [1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[false,false],[true,false]] := by decide
#print axioms case0450
theorem case0451 : minimalVertices [0,1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0451
theorem case0452 : minimalVertices [0,0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,true],[true],[true,true]] ∧ terminals [0,0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[false,true],[true,true]] := by decide
#print axioms case0452
theorem case0453 : minimalVertices [0,1,0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0453
theorem case0454 : minimalVertices [25] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [] ∧ terminals [25] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms case0454
theorem case0455 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [] ∧ terminals [] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms case0455
theorem case0456 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[false,true]] ∧ terminals [0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[false,true]] := by decide
#print axioms case0456
theorem case0457 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,false],[true],[true,false],[true,true]] ∧ terminals [1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[false,false],[true,false],[true,true]] := by decide
#print axioms case0457
theorem case0458 : minimalVertices [0,1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0458
theorem case0459 : minimalVertices [0,0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[false,true]] ∧ terminals [0,0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[false,true]] := by decide
#print axioms case0459
theorem case0460 : minimalVertices [0,1,0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0460
theorem case0461 : minimalVertices [25] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [] ∧ terminals [25] (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms case0461
theorem case0462 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [] ∧ terminals [] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms case0462
theorem case0463 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[true],[true,false],[true,true]] ∧ terminals [0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[true,false],[true,true]] := by decide
#print axioms case0463
theorem case0464 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[false],[false,false],[false,true]] ∧ terminals [1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[false,false],[false,true]] := by decide
#print axioms case0464
theorem case0465 : minimalVertices [0,1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0465
theorem case0466 : minimalVertices [0,0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[true],[true,false],[true,true]] ∧ terminals [0,0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[true,false],[true,true]] := by decide
#print axioms case0466
theorem case0467 : minimalVertices [0,1,0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0467
theorem case0468 : minimalVertices [25] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [] ∧ terminals [25] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) = [] := by decide
#print axioms case0468
theorem case0469 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [] ∧ terminals [] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms case0469
theorem case0470 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[true,false]] ∧ terminals [0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[true,false]] := by decide
#print axioms case0470
theorem case0471 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,true]] ∧ terminals [1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[false,false],[false,true],[true,true]] := by decide
#print axioms case0471
theorem case0472 : minimalVertices [0,1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0472
theorem case0473 : minimalVertices [0,0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[true,false]] ∧ terminals [0,0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[true,false]] := by decide
#print axioms case0473
theorem case0474 : minimalVertices [0,1,0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0474
theorem case0475 : minimalVertices [25] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [] ∧ terminals [25] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) = [] := by decide
#print axioms case0475
theorem case0476 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [] ∧ terminals [] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms case0476
theorem case0477 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[true,true]] ∧ terminals [0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[true,true]] := by decide
#print axioms case0477
theorem case0478 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false]] ∧ terminals [1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[false,false],[false,true],[true,false]] := by decide
#print axioms case0478
theorem case0479 : minimalVertices [0,1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0479
theorem case0480 : minimalVertices [0,0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[true,true]] ∧ terminals [0,0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[true,true]] := by decide
#print axioms case0480
theorem case0481 : minimalVertices [0,1,0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0481
theorem case0482 : minimalVertices [25] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [] ∧ terminals [25] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) = [] := by decide
#print axioms case0482
theorem case0483 : minimalVertices [] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] ∧ terminals [] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms case0483
theorem case0484 : minimalVertices [0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] ∧ terminals [0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms case0484
theorem case0485 : minimalVertices [1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0485
theorem case0486 : minimalVertices [0,1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0486
theorem case0487 : minimalVertices [0,0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] ∧ terminals [0,0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms case0487
theorem case0488 : minimalVertices [0,1,0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[],[false],[false,false],[false,true],[true],[true,false],[true,true]] ∧ terminals [0,1,0] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [[false,false],[false,true],[true,false],[true,true]] := by decide
#print axioms case0488
theorem case0489 : minimalVertices [25] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] ∧ terminals [25] (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) = [] := by decide
#print axioms case0489
theorem case0490 : minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [] ∧ terminals [] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [] := by decide
#print axioms case0490
theorem case0491 : minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0491
theorem case0492 : minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [] ∧ terminals [1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [] := by decide
#print axioms case0492
theorem case0493 : minimalVertices [0,1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0493
theorem case0494 : minimalVertices [0,0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0494
theorem case0495 : minimalVertices [0,1,0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0495
theorem case0496 : minimalVertices [25] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [] ∧ terminals [25] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [] := by decide
#print axioms case0496
theorem case0497 : minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [] ∧ terminals [] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [] := by decide
#print axioms case0497
theorem case0498 : minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[false],[false,false],[false,true],[false,true,false],[false,true,true]] ∧ terminals [0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[false,false],[false,true,false],[false,true,true]] := by decide
#print axioms case0498
theorem case0499 : minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[true]] ∧ terminals [1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[true]] := by decide
#print axioms case0499
theorem case0500 : minimalVertices [0,1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0500
theorem case0501 : minimalVertices [0,0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[false],[false,false],[false,true],[false,true,false],[false,true,true]] ∧ terminals [0,0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[false,false],[false,true,false],[false,true,true]] := by decide
#print axioms case0501
theorem case0502 : minimalVertices [0,1,0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0502
theorem case0503 : minimalVertices [25] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [] ∧ terminals [25] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [] := by decide
#print axioms case0503
theorem case0504 : minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [] ∧ terminals [] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [] := by decide
#print axioms case0504
theorem case0505 : minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[true]] ∧ terminals [0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[false,false],[false,true,false],[true]] := by decide
#print axioms case0505
theorem case0506 : minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[false,true,true]] ∧ terminals [1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[false,true,true]] := by decide
#print axioms case0506
theorem case0507 : minimalVertices [0,1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0507
theorem case0508 : minimalVertices [0,0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[true]] ∧ terminals [0,0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[false,false],[false,true,false],[true]] := by decide
#print axioms case0508
theorem case0509 : minimalVertices [0,1,0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0509
theorem case0510 : minimalVertices [25] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [] ∧ terminals [25] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [] := by decide
#print axioms case0510
theorem case0511 : minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [] ∧ terminals [] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [] := by decide
#print axioms case0511
theorem case0512 : minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[false],[false,false],[false,true],[false,true,false]] ∧ terminals [0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[false,false],[false,true,false]] := by decide
#print axioms case0512
theorem case0513 : minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[],[false],[false,true],[false,true,true],[true]] ∧ terminals [1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[false,true,true],[true]] := by decide
#print axioms case0513
theorem case0514 : minimalVertices [0,1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0514
theorem case0515 : minimalVertices [0,0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[false],[false,false],[false,true],[false,true,false]] ∧ terminals [0,0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[false,false],[false,true,false]] := by decide
#print axioms case0515
theorem case0516 : minimalVertices [0,1,0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0516
theorem case0517 : minimalVertices [25] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [] ∧ terminals [25] (.node (.node (.leaf 0) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [] := by decide
#print axioms case0517
theorem case0518 : minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [] ∧ terminals [] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [] := by decide
#print axioms case0518
theorem case0519 : minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,true],[true]] ∧ terminals [0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[false,false],[false,true,true],[true]] := by decide
#print axioms case0519
theorem case0520 : minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[false,true,false]] ∧ terminals [1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[false,true,false]] := by decide
#print axioms case0520
theorem case0521 : minimalVertices [0,1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0521
theorem case0522 : minimalVertices [0,0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,true],[true]] ∧ terminals [0,0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[false,false],[false,true,true],[true]] := by decide
#print axioms case0522
theorem case0523 : minimalVertices [0,1,0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0523
theorem case0524 : minimalVertices [25] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [] ∧ terminals [25] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [] := by decide
#print axioms case0524
theorem case0525 : minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [] ∧ terminals [] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [] := by decide
#print axioms case0525
theorem case0526 : minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[false],[false,false],[false,true],[false,true,true]] ∧ terminals [0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[false,false],[false,true,true]] := by decide
#print axioms case0526
theorem case0527 : minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[],[false],[false,true],[false,true,false],[true]] ∧ terminals [1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[false,true,false],[true]] := by decide
#print axioms case0527
theorem case0528 : minimalVertices [0,1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0528
theorem case0529 : minimalVertices [0,0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[false],[false,false],[false,true],[false,true,true]] ∧ terminals [0,0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[false,false],[false,true,true]] := by decide
#print axioms case0529
theorem case0530 : minimalVertices [0,1,0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0530
theorem case0531 : minimalVertices [25] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [] ∧ terminals [25] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [] := by decide
#print axioms case0531
theorem case0532 : minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [] ∧ terminals [] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [] := by decide
#print axioms case0532
theorem case0533 : minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[true]] ∧ terminals [0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[false,false],[true]] := by decide
#print axioms case0533
theorem case0534 : minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[false,true],[false,true,false],[false,true,true]] ∧ terminals [1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[false,true,false],[false,true,true]] := by decide
#print axioms case0534
theorem case0535 : minimalVertices [0,1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0535
theorem case0536 : minimalVertices [0,0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[true]] ∧ terminals [0,0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[false,false],[true]] := by decide
#print axioms case0536
theorem case0537 : minimalVertices [0,1,0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0537
theorem case0538 : minimalVertices [25] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [] ∧ terminals [25] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [] := by decide
#print axioms case0538
theorem case0539 : minimalVertices [] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] ∧ terminals [] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] := by decide
#print axioms case0539
theorem case0540 : minimalVertices [0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[false,false]] ∧ terminals [0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[false,false]] := by decide
#print axioms case0540
theorem case0541 : minimalVertices [1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[],[false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0541
theorem case0542 : minimalVertices [0,1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0542
theorem case0543 : minimalVertices [0,0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[false,false]] ∧ terminals [0,0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[false,false]] := by decide
#print axioms case0543
theorem case0544 : minimalVertices [0,1,0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0544
theorem case0545 : minimalVertices [25] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] ∧ terminals [25] (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] := by decide
#print axioms case0545
theorem case0546 : minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [] ∧ terminals [] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [] := by decide
#print axioms case0546
theorem case0547 : minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[],[false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0547
theorem case0548 : minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[false,false]] ∧ terminals [1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[false,false]] := by decide
#print axioms case0548
theorem case0549 : minimalVertices [0,1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0549
theorem case0550 : minimalVertices [0,0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[],[false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0550
theorem case0551 : minimalVertices [0,1,0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0551
theorem case0552 : minimalVertices [25] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [] ∧ terminals [25] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 0)) = [] := by decide
#print axioms case0552
theorem case0553 : minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [] ∧ terminals [] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [] := by decide
#print axioms case0553
theorem case0554 : minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[false,true],[false,true,false],[false,true,true]] ∧ terminals [0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[false,true,false],[false,true,true]] := by decide
#print axioms case0554
theorem case0555 : minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[],[false],[false,false],[true]] ∧ terminals [1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[false,false],[true]] := by decide
#print axioms case0555
theorem case0556 : minimalVertices [0,1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0556
theorem case0557 : minimalVertices [0,0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[false,true],[false,true,false],[false,true,true]] ∧ terminals [0,0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[false,true,false],[false,true,true]] := by decide
#print axioms case0557
theorem case0558 : minimalVertices [0,1,0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0558
theorem case0559 : minimalVertices [25] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [] ∧ terminals [25] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 0))) (.leaf 1)) = [] := by decide
#print axioms case0559
theorem case0560 : minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [] ∧ terminals [] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [] := by decide
#print axioms case0560
theorem case0561 : minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[],[false],[false,true],[false,true,false],[true]] ∧ terminals [0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[false,true,false],[true]] := by decide
#print axioms case0561
theorem case0562 : minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[false],[false,false],[false,true],[false,true,true]] ∧ terminals [1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[false,false],[false,true,true]] := by decide
#print axioms case0562
theorem case0563 : minimalVertices [0,1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0563
theorem case0564 : minimalVertices [0,0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[],[false],[false,true],[false,true,false],[true]] ∧ terminals [0,0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[false,true,false],[true]] := by decide
#print axioms case0564
theorem case0565 : minimalVertices [0,1,0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0565
theorem case0566 : minimalVertices [25] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [] ∧ terminals [25] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 0)) = [] := by decide
#print axioms case0566
theorem case0567 : minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [] ∧ terminals [] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [] := by decide
#print axioms case0567
theorem case0568 : minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[false,true,false]] ∧ terminals [0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[false,true,false]] := by decide
#print axioms case0568
theorem case0569 : minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,true],[true]] ∧ terminals [1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[false,false],[false,true,true],[true]] := by decide
#print axioms case0569
theorem case0570 : minimalVertices [0,1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0570
theorem case0571 : minimalVertices [0,0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[false,true,false]] ∧ terminals [0,0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[false,true,false]] := by decide
#print axioms case0571
theorem case0572 : minimalVertices [0,1,0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0572
theorem case0573 : minimalVertices [25] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [] ∧ terminals [25] (.node (.node (.leaf 1) (.node (.leaf 0) (.leaf 1))) (.leaf 1)) = [] := by decide
#print axioms case0573
theorem case0574 : minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [] ∧ terminals [] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [] := by decide
#print axioms case0574
theorem case0575 : minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[],[false],[false,true],[false,true,true],[true]] ∧ terminals [0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[false,true,true],[true]] := by decide
#print axioms case0575
theorem case0576 : minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[false],[false,false],[false,true],[false,true,false]] ∧ terminals [1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[false,false],[false,true,false]] := by decide
#print axioms case0576
theorem case0577 : minimalVertices [0,1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0577
theorem case0578 : minimalVertices [0,0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[],[false],[false,true],[false,true,true],[true]] ∧ terminals [0,0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[false,true,true],[true]] := by decide
#print axioms case0578
theorem case0579 : minimalVertices [0,1,0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0579
theorem case0580 : minimalVertices [25] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [] ∧ terminals [25] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 0)) = [] := by decide
#print axioms case0580
theorem case0581 : minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [] ∧ terminals [] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [] := by decide
#print axioms case0581
theorem case0582 : minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[false,true,true]] ∧ terminals [0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[false,true,true]] := by decide
#print axioms case0582
theorem case0583 : minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[true]] ∧ terminals [1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[false,false],[false,true,false],[true]] := by decide
#print axioms case0583
theorem case0584 : minimalVertices [0,1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0584
theorem case0585 : minimalVertices [0,0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[false,true,true]] ∧ terminals [0,0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[false,true,true]] := by decide
#print axioms case0585
theorem case0586 : minimalVertices [0,1,0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0586
theorem case0587 : minimalVertices [25] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [] ∧ terminals [25] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 0))) (.leaf 1)) = [] := by decide
#print axioms case0587
theorem case0588 : minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [] ∧ terminals [] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [] := by decide
#print axioms case0588
theorem case0589 : minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[true]] ∧ terminals [0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[true]] := by decide
#print axioms case0589
theorem case0590 : minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[false],[false,false],[false,true],[false,true,false],[false,true,true]] ∧ terminals [1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[false,false],[false,true,false],[false,true,true]] := by decide
#print axioms case0590
theorem case0591 : minimalVertices [0,1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0591
theorem case0592 : minimalVertices [0,0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[true]] ∧ terminals [0,0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[true]] := by decide
#print axioms case0592
theorem case0593 : minimalVertices [0,1,0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0593
theorem case0594 : minimalVertices [25] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [] ∧ terminals [25] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 0)) = [] := by decide
#print axioms case0594
theorem case0595 : minimalVertices [] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] ∧ terminals [] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] := by decide
#print axioms case0595
theorem case0596 : minimalVertices [0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] ∧ terminals [0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] := by decide
#print axioms case0596
theorem case0597 : minimalVertices [1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0597
theorem case0598 : minimalVertices [0,1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0598
theorem case0599 : minimalVertices [0,0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] ∧ terminals [0,0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] := by decide
#print axioms case0599
theorem case0600 : minimalVertices [0,1,0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[],[false],[false,false],[false,true],[false,true,false],[false,true,true],[true]] ∧ terminals [0,1,0] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [[false,false],[false,true,false],[false,true,true],[true]] := by decide
#print axioms case0600
theorem case0601 : minimalVertices [25] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] ∧ terminals [25] (.node (.node (.leaf 1) (.node (.leaf 1) (.leaf 1))) (.leaf 1)) = [] := by decide
#print axioms case0601
theorem case0602 : minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [] ∧ terminals [] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms case0602
theorem case0603 : minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0603
theorem case0604 : minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [] ∧ terminals [1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms case0604
theorem case0605 : minimalVertices [0,1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0605
theorem case0606 : minimalVertices [0,0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0606
theorem case0607 : minimalVertices [0,1,0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0607
theorem case0608 : minimalVertices [25] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [] ∧ terminals [25] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms case0608
theorem case0609 : minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [] ∧ terminals [] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms case0609
theorem case0610 : minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[false],[false,false],[false,false,false],[false,false,true],[false,true]] ∧ terminals [0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[false,false,false],[false,false,true],[false,true]] := by decide
#print axioms case0610
theorem case0611 : minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[true]] ∧ terminals [1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[true]] := by decide
#print axioms case0611
theorem case0612 : minimalVertices [0,1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0612
theorem case0613 : minimalVertices [0,0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[false],[false,false],[false,false,false],[false,false,true],[false,true]] ∧ terminals [0,0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[false,false,false],[false,false,true],[false,true]] := by decide
#print axioms case0613
theorem case0614 : minimalVertices [0,1,0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0614
theorem case0615 : minimalVertices [25] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [] ∧ terminals [25] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms case0615
theorem case0616 : minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [] ∧ terminals [] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms case0616
theorem case0617 : minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[true]] ∧ terminals [0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[false,false,false],[false,false,true],[true]] := by decide
#print axioms case0617
theorem case0618 : minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[false,true]] ∧ terminals [1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[false,true]] := by decide
#print axioms case0618
theorem case0619 : minimalVertices [0,1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0619
theorem case0620 : minimalVertices [0,0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[true]] ∧ terminals [0,0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[false,false,false],[false,false,true],[true]] := by decide
#print axioms case0620
theorem case0621 : minimalVertices [0,1,0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0621
theorem case0622 : minimalVertices [25] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [] ∧ terminals [25] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms case0622
theorem case0623 : minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [] ∧ terminals [] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms case0623
theorem case0624 : minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[false,false],[false,false,false],[false,false,true]] ∧ terminals [0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[false,false,false],[false,false,true]] := by decide
#print axioms case0624
theorem case0625 : minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,true],[true]] ∧ terminals [1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[false,true],[true]] := by decide
#print axioms case0625
theorem case0626 : minimalVertices [0,1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0626
theorem case0627 : minimalVertices [0,0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[false,false],[false,false,false],[false,false,true]] ∧ terminals [0,0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[false,false,false],[false,false,true]] := by decide
#print axioms case0627
theorem case0628 : minimalVertices [0,1,0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0628
theorem case0629 : minimalVertices [25] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [] ∧ terminals [25] (.node (.node (.node (.leaf 0) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms case0629
theorem case0630 : minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [] ∧ terminals [] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms case0630
theorem case0631 : minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,true],[true]] ∧ terminals [0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[false,false,false],[false,true],[true]] := by decide
#print axioms case0631
theorem case0632 : minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[false,false,true]] ∧ terminals [1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[false,false,true]] := by decide
#print axioms case0632
theorem case0633 : minimalVertices [0,1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0633
theorem case0634 : minimalVertices [0,0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,true],[true]] ∧ terminals [0,0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[false,false,false],[false,true],[true]] := by decide
#print axioms case0634
theorem case0635 : minimalVertices [0,1,0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0635
theorem case0636 : minimalVertices [25] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [] ∧ terminals [25] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms case0636
theorem case0637 : minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [] ∧ terminals [] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms case0637
theorem case0638 : minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[false],[false,false],[false,false,false],[false,true]] ∧ terminals [0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[false,false,false],[false,true]] := by decide
#print axioms case0638
theorem case0639 : minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,true],[true]] ∧ terminals [1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[false,false,true],[true]] := by decide
#print axioms case0639
theorem case0640 : minimalVertices [0,1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0640
theorem case0641 : minimalVertices [0,0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[false],[false,false],[false,false,false],[false,true]] ∧ terminals [0,0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[false,false,false],[false,true]] := by decide
#print axioms case0641
theorem case0642 : minimalVertices [0,1,0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0642
theorem case0643 : minimalVertices [25] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [] ∧ terminals [25] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms case0643
theorem case0644 : minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [] ∧ terminals [] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms case0644
theorem case0645 : minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[true]] ∧ terminals [0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[false,false,false],[true]] := by decide
#print axioms case0645
theorem case0646 : minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[false],[false,false],[false,false,true],[false,true]] ∧ terminals [1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[false,false,true],[false,true]] := by decide
#print axioms case0646
theorem case0647 : minimalVertices [0,1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0647
theorem case0648 : minimalVertices [0,0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[true]] ∧ terminals [0,0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[false,false,false],[true]] := by decide
#print axioms case0648
theorem case0649 : minimalVertices [0,1,0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0649
theorem case0650 : minimalVertices [25] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [] ∧ terminals [25] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms case0650
theorem case0651 : minimalVertices [] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] ∧ terminals [] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms case0651
theorem case0652 : minimalVertices [0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[false,false,false]] ∧ terminals [0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[false,false,false]] := by decide
#print axioms case0652
theorem case0653 : minimalVertices [1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,true],[false,true],[true]] ∧ terminals [1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[false,false,true],[false,true],[true]] := by decide
#print axioms case0653
theorem case0654 : minimalVertices [0,1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0654
theorem case0655 : minimalVertices [0,0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[false,false,false]] ∧ terminals [0,0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[false,false,false]] := by decide
#print axioms case0655
theorem case0656 : minimalVertices [0,1,0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0656
theorem case0657 : minimalVertices [25] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] ∧ terminals [25] (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms case0657
theorem case0658 : minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [] ∧ terminals [] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms case0658
theorem case0659 : minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,true],[false,true],[true]] ∧ terminals [0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[false,false,true],[false,true],[true]] := by decide
#print axioms case0659
theorem case0660 : minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[false,false,false]] ∧ terminals [1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[false,false,false]] := by decide
#print axioms case0660
theorem case0661 : minimalVertices [0,1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0661
theorem case0662 : minimalVertices [0,0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[false,false,true],[false,true],[true]] := by decide
#print axioms case0662
theorem case0663 : minimalVertices [0,1,0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0663
theorem case0664 : minimalVertices [25] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [] ∧ terminals [25] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms case0664
theorem case0665 : minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [] ∧ terminals [] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms case0665
theorem case0666 : minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[false],[false,false],[false,false,true],[false,true]] ∧ terminals [0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[false,false,true],[false,true]] := by decide
#print axioms case0666
theorem case0667 : minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[true]] ∧ terminals [1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[false,false,false],[true]] := by decide
#print axioms case0667
theorem case0668 : minimalVertices [0,1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0668
theorem case0669 : minimalVertices [0,0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[false],[false,false],[false,false,true],[false,true]] ∧ terminals [0,0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[false,false,true],[false,true]] := by decide
#print axioms case0669
theorem case0670 : minimalVertices [0,1,0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0670
theorem case0671 : minimalVertices [25] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [] ∧ terminals [25] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms case0671
theorem case0672 : minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [] ∧ terminals [] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms case0672
theorem case0673 : minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,true],[true]] ∧ terminals [0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[false,false,true],[true]] := by decide
#print axioms case0673
theorem case0674 : minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[false],[false,false],[false,false,false],[false,true]] ∧ terminals [1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[false,false,false],[false,true]] := by decide
#print axioms case0674
theorem case0675 : minimalVertices [0,1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0675
theorem case0676 : minimalVertices [0,0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,true],[true]] ∧ terminals [0,0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[false,false,true],[true]] := by decide
#print axioms case0676
theorem case0677 : minimalVertices [0,1,0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0677
theorem case0678 : minimalVertices [25] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [] ∧ terminals [25] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms case0678
theorem case0679 : minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [] ∧ terminals [] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms case0679
theorem case0680 : minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[false,false,true]] ∧ terminals [0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[false,false,true]] := by decide
#print axioms case0680
theorem case0681 : minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,true],[true]] ∧ terminals [1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[false,false,false],[false,true],[true]] := by decide
#print axioms case0681
theorem case0682 : minimalVertices [0,1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0682
theorem case0683 : minimalVertices [0,0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[false,false,true]] ∧ terminals [0,0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[false,false,true]] := by decide
#print axioms case0683
theorem case0684 : minimalVertices [0,1,0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0684
theorem case0685 : minimalVertices [25] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [] ∧ terminals [25] (.node (.node (.node (.leaf 1) (.leaf 0)) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms case0685
theorem case0686 : minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [] ∧ terminals [] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms case0686
theorem case0687 : minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,true],[true]] ∧ terminals [0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[false,true],[true]] := by decide
#print axioms case0687
theorem case0688 : minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[false,false],[false,false,false],[false,false,true]] ∧ terminals [1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[false,false,false],[false,false,true]] := by decide
#print axioms case0688
theorem case0689 : minimalVertices [0,1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0689
theorem case0690 : minimalVertices [0,0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,true],[true]] ∧ terminals [0,0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[false,true],[true]] := by decide
#print axioms case0690
theorem case0691 : minimalVertices [0,1,0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0691
theorem case0692 : minimalVertices [25] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [] ∧ terminals [25] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 0)) = [] := by decide
#print axioms case0692
theorem case0693 : minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [] ∧ terminals [] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms case0693
theorem case0694 : minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[false,true]] ∧ terminals [0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[false,true]] := by decide
#print axioms case0694
theorem case0695 : minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[true]] ∧ terminals [1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[false,false,false],[false,false,true],[true]] := by decide
#print axioms case0695
theorem case0696 : minimalVertices [0,1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0696
theorem case0697 : minimalVertices [0,0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[false,true]] ∧ terminals [0,0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[false,true]] := by decide
#print axioms case0697
theorem case0698 : minimalVertices [0,1,0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0698
theorem case0699 : minimalVertices [25] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [] ∧ terminals [25] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 0)) (.leaf 1)) = [] := by decide
#print axioms case0699
theorem case0700 : minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [] ∧ terminals [] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms case0700
theorem case0701 : minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[true]] ∧ terminals [0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[true]] := by decide
#print axioms case0701
theorem case0702 : minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[false],[false,false],[false,false,false],[false,false,true],[false,true]] ∧ terminals [1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[false,false,false],[false,false,true],[false,true]] := by decide
#print axioms case0702
theorem case0703 : minimalVertices [0,1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0703
theorem case0704 : minimalVertices [0,0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[true]] ∧ terminals [0,0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[true]] := by decide
#print axioms case0704
theorem case0705 : minimalVertices [0,1,0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0705
theorem case0706 : minimalVertices [25] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [] ∧ terminals [25] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 0)) = [] := by decide
#print axioms case0706
theorem case0707 : minimalVertices [] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] ∧ terminals [] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms case0707
theorem case0708 : minimalVertices [0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] ∧ terminals [0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms case0708
theorem case0709 : minimalVertices [1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0709
theorem case0710 : minimalVertices [0,1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0710
theorem case0711 : minimalVertices [0,0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] ∧ terminals [0,0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms case0711
theorem case0712 : minimalVertices [0,1,0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[],[false],[false,false],[false,false,false],[false,false,true],[false,true],[true]] ∧ terminals [0,1,0] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [[false,false,false],[false,false,true],[false,true],[true]] := by decide
#print axioms case0712
theorem case0713 : minimalVertices [25] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] ∧ terminals [25] (.node (.node (.node (.leaf 1) (.leaf 1)) (.leaf 1)) (.leaf 1)) = [] := by decide
#print axioms case0713
end FreshSourcePanel
