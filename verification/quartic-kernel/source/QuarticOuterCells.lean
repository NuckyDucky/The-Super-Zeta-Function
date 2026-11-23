import QuarticPointwise1051
import QuarticPointwise1073
import QuarticPointwise1095
import Mathlib.Tactic.IntervalCases

open Set
namespace QuarticGrid

theorem encloses_outer_core (j : ℕ) (hlo : 1051 ≤ j) (hhi : j < 1116) (x : ℝ)
    (hx : x ∈ Icc (node j : ℝ) (node (j+1) : ℝ)) :
    (lowerK j : ℝ) ≤ QuarticKernel.kernel x ∧ QuarticKernel.kernel x ≤ (upperK j : ℝ) := by
  interval_cases j
  · exact cell_1051 x hx
  · exact cell_1052 x hx
  · exact cell_1053 x hx
  · exact cell_1054 x hx
  · exact cell_1055 x hx
  · exact cell_1056 x hx
  · exact cell_1057 x hx
  · exact cell_1058 x hx
  · exact cell_1059 x hx
  · exact cell_1060 x hx
  · exact cell_1061 x hx
  · exact cell_1062 x hx
  · exact cell_1063 x hx
  · exact cell_1064 x hx
  · exact cell_1065 x hx
  · exact cell_1066 x hx
  · exact cell_1067 x hx
  · exact cell_1068 x hx
  · exact cell_1069 x hx
  · exact cell_1070 x hx
  · exact cell_1071 x hx
  · exact cell_1072 x hx
  · exact cell_1073 x hx
  · exact cell_1074 x hx
  · exact cell_1075 x hx
  · exact cell_1076 x hx
  · exact cell_1077 x hx
  · exact cell_1078 x hx
  · exact cell_1079 x hx
  · exact cell_1080 x hx
  · exact cell_1081 x hx
  · exact cell_1082 x hx
  · exact cell_1083 x hx
  · exact cell_1084 x hx
  · exact cell_1085 x hx
  · exact cell_1086 x hx
  · exact cell_1087 x hx
  · exact cell_1088 x hx
  · exact cell_1089 x hx
  · exact cell_1090 x hx
  · exact cell_1091 x hx
  · exact cell_1092 x hx
  · exact cell_1093 x hx
  · exact cell_1094 x hx
  · exact cell_1095 x hx
  · exact cell_1096 x hx
  · exact cell_1097 x hx
  · exact cell_1098 x hx
  · exact cell_1099 x hx
  · exact cell_1100 x hx
  · exact cell_1101 x hx
  · exact cell_1102 x hx
  · exact cell_1103 x hx
  · exact cell_1104 x hx
  · exact cell_1105 x hx
  · exact cell_1106 x hx
  · exact cell_1107 x hx
  · exact cell_1108 x hx
  · exact cell_1109 x hx
  · exact cell_1110 x hx
  · exact cell_1111 x hx
  · exact cell_1112 x hx
  · exact cell_1113 x hx
  · exact cell_1114 x hx
  · exact cell_1115 x hx

#print axioms encloses_outer_core

end QuarticGrid

