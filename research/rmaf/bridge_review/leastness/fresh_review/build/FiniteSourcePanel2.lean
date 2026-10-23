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
end FreshSourcePanel
