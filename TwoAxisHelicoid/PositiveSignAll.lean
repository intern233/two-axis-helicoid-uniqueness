import TwoAxisHelicoid.FiniteIntervalChain
import TwoAxisHelicoid.PositiveChordBox1000
import TwoAxisHelicoid.PositiveChordBox1001
import TwoAxisHelicoid.PositiveChordBox1002
import TwoAxisHelicoid.PositiveChordBox1003
import TwoAxisHelicoid.PositiveChordBox1004
import TwoAxisHelicoid.PositiveChordBox1005
import TwoAxisHelicoid.PositiveChordBox1006
import TwoAxisHelicoid.PositiveChordBox1007
import TwoAxisHelicoid.PositiveChordBox1008
import TwoAxisHelicoid.PositiveChordBox1009
import TwoAxisHelicoid.PositiveChordBox1010
import TwoAxisHelicoid.PositiveChordBox1011
import TwoAxisHelicoid.PositiveChordBox1012
import TwoAxisHelicoid.PositiveChordBox1013
import TwoAxisHelicoid.PositiveChordBox1014
import TwoAxisHelicoid.PositiveChordBox1015
import TwoAxisHelicoid.PositiveChordBox1016
import TwoAxisHelicoid.PositiveChordBox1017
import TwoAxisHelicoid.PositiveChordBox1018
import TwoAxisHelicoid.PositiveChordBox1019
import TwoAxisHelicoid.PositiveChordBox1020
import TwoAxisHelicoid.PositiveChordBox1021
import TwoAxisHelicoid.PositiveChordBox1022
import TwoAxisHelicoid.PositiveChordBox1023
import TwoAxisHelicoid.PositiveChordBox1024
import TwoAxisHelicoid.PositiveChordBox1025
import TwoAxisHelicoid.PositiveChordBox1026
import TwoAxisHelicoid.PositiveChordBox1027
import TwoAxisHelicoid.PositiveChordBox1028
import TwoAxisHelicoid.PositiveChordBox1029
import TwoAxisHelicoid.PositiveChordBox1030
import TwoAxisHelicoid.PositiveChordBox1031
import TwoAxisHelicoid.PositiveChordBox1032
import TwoAxisHelicoid.PositiveChordBox1033
import TwoAxisHelicoid.PositiveChordBox1034
import TwoAxisHelicoid.PositiveChordBox1035
import TwoAxisHelicoid.PositiveChordBox1036
import TwoAxisHelicoid.PositiveChordBox1037
import TwoAxisHelicoid.PositiveChordBox1038
import TwoAxisHelicoid.PositiveChordBox1039
import TwoAxisHelicoid.PositiveChordBox1040
import TwoAxisHelicoid.PositiveChordBox1041
import TwoAxisHelicoid.PositiveChordBox1042
import TwoAxisHelicoid.PositiveChordBox1043
import TwoAxisHelicoid.PositiveChordBox1044
import TwoAxisHelicoid.PositiveChordBox1045
import TwoAxisHelicoid.PositiveChordBox1046
import TwoAxisHelicoid.PositiveChordBox1047
import TwoAxisHelicoid.PositiveChordBox1048
import TwoAxisHelicoid.PositiveChordBox1049
import TwoAxisHelicoid.PositiveChordBox1050
import TwoAxisHelicoid.PositiveChordBox1051
import TwoAxisHelicoid.PositiveChordBox1052
import TwoAxisHelicoid.PositiveChordBox1053
import TwoAxisHelicoid.PositiveChordBox1054
import TwoAxisHelicoid.PositiveChordBox1055
import TwoAxisHelicoid.PositiveChordBox1056
import TwoAxisHelicoid.PositiveChordBox1057
import TwoAxisHelicoid.PositiveChordBox1058
import TwoAxisHelicoid.PositiveChordBox1059
import TwoAxisHelicoid.PositiveChordBox1060
import TwoAxisHelicoid.PositiveChordBox1061
import TwoAxisHelicoid.PositiveChordBox1062
import TwoAxisHelicoid.PositiveChordBox1063
import TwoAxisHelicoid.PositiveChordBox1064
import TwoAxisHelicoid.PositiveChordBox1065
import TwoAxisHelicoid.PositiveChordBox1066
import TwoAxisHelicoid.PositiveChordBox1067
import TwoAxisHelicoid.PositiveChordBox1068
import TwoAxisHelicoid.PositiveChordBox1069
import TwoAxisHelicoid.PositiveChordBox1070
import TwoAxisHelicoid.PositiveChordBox1071
import TwoAxisHelicoid.PositiveChordBox1072
import TwoAxisHelicoid.PositiveChordBox1073
import TwoAxisHelicoid.PositiveChordBox1074
import TwoAxisHelicoid.PositiveChordBox1075
import TwoAxisHelicoid.PositiveChordBox1076
import TwoAxisHelicoid.PositiveChordBox1077
import TwoAxisHelicoid.PositiveChordBox1078
import TwoAxisHelicoid.PositiveChordBox1079
import TwoAxisHelicoid.PositiveChordBox1080
import TwoAxisHelicoid.PositiveChordBox1081
import TwoAxisHelicoid.PositiveChordBox1082
import TwoAxisHelicoid.PositiveChordBox1083
import TwoAxisHelicoid.PositiveChordBox1084
import TwoAxisHelicoid.PositiveChordBox1085
import TwoAxisHelicoid.PositiveChordBox1086
import TwoAxisHelicoid.PositiveChordBox1087
import TwoAxisHelicoid.PositiveChordBox1088
import TwoAxisHelicoid.PositiveChordBox1089
import TwoAxisHelicoid.PositiveChordBox1090
import TwoAxisHelicoid.PositiveChordBox1091
import TwoAxisHelicoid.PositiveChordBox1092
import TwoAxisHelicoid.PositiveChordBox1093
import TwoAxisHelicoid.PositiveChordBox1094
import TwoAxisHelicoid.PositiveChordBox1095
import TwoAxisHelicoid.PositiveChordBox1096
import TwoAxisHelicoid.PositiveChordBox1097
import TwoAxisHelicoid.PositiveChordBox1098

namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def positiveChordParameterBoundary : ℕ → ℚ := fun i => match i with
  | 0 => (1/8)
  | 1 => (21/160)
  | 2 => (11/80)
  | 3 => (23/160)
  | 4 => (3/20)
  | 5 => (13/80)
  | 6 => (7/40)
  | 7 => (3/16)
  | 8 => (1/5)
  | 9 => (9/40)
  | 10 => (1/4)
  | 11 => (11/40)
  | 12 => (3/10)
  | 13 => (13/40)
  | 14 => (7/20)
  | 15 => (3/8)
  | 16 => (2/5)
  | 17 => (33/80)
  | 18 => (17/40)
  | 19 => (7/16)
  | 20 => (9/20)
  | 21 => (37/80)
  | 22 => (19/40)
  | 23 => (39/80)
  | 24 => (1/2)
  | 25 => (41/80)
  | 26 => (21/40)
  | 27 => (43/80)
  | 28 => (11/20)
  | 29 => (9/16)
  | 30 => (23/40)
  | 31 => (47/80)
  | 32 => (3/5)
  | 33 => (49/80)
  | 34 => (5/8)
  | 35 => (101/160)
  | 36 => (51/80)
  | 37 => (103/160)
  | 38 => (13/20)
  | 39 => (21/32)
  | 40 => (53/80)
  | 41 => (107/160)
  | 42 => (27/40)
  | 43 => (109/160)
  | 44 => (11/16)
  | 45 => (111/160)
  | 46 => (7/10)
  | 47 => (113/160)
  | 48 => (57/80)
  | 49 => (23/32)
  | 50 => (29/40)
  | 51 => (117/160)
  | 52 => (59/80)
  | 53 => (119/160)
  | 54 => (3/4)
  | 55 => (121/160)
  | 56 => (61/80)
  | 57 => (49/64)
  | 58 => (123/160)
  | 59 => (247/320)
  | 60 => (31/40)
  | 61 => (249/320)
  | 62 => (25/32)
  | 63 => (251/320)
  | 64 => (63/80)
  | 65 => (253/320)
  | 66 => (127/160)
  | 67 => (51/64)
  | 68 => (4/5)
  | 69 => (257/320)
  | 70 => (129/160)
  | 71 => (259/320)
  | 72 => (13/16)
  | 73 => (261/320)
  | 74 => (131/160)
  | 75 => (105/128)
  | 76 => (263/320)
  | 77 => (527/640)
  | 78 => (33/40)
  | 79 => (529/640)
  | 80 => (53/64)
  | 81 => (531/640)
  | 82 => (133/160)
  | 83 => (533/640)
  | 84 => (267/320)
  | 85 => (107/128)
  | 86 => (67/80)
  | 87 => (537/640)
  | 88 => (269/320)
  | 89 => (539/640)
  | 90 => (1079/1280)
  | 91 => (27/32)
  | 92 => (1081/1280)
  | 93 => (541/640)
  | 94 => (1083/1280)
  | 95 => (271/320)
  | 96 => (217/256)
  | 97 => (543/640)
  | 98 => (1087/1280)
  | _ => (17/20)

theorem actualPeriodAlong_positive_compact {t : ℝ}
    (htl : ((1/8) : ℝ) ≤ t)
    (htu : t ≤ ((17/20) : ℝ)) :
    (3/10000 : ℝ) < actualPeriodAlong t := by
  apply predicate_on_interval_chain 98 (fun i => (positiveChordParameterBoundary i : ℝ))
    (fun x => (3/10000 : ℝ) < actualPeriodAlong x)
  · intro i x hxl hxu
    fin_cases i
    · exact positiveChordBox1000_positive hxl hxu
    · exact positiveChordBox1001_positive hxl hxu
    · exact positiveChordBox1002_positive hxl hxu
    · exact positiveChordBox1003_positive hxl hxu
    · exact positiveChordBox1004_positive hxl hxu
    · exact positiveChordBox1005_positive hxl hxu
    · exact positiveChordBox1006_positive hxl hxu
    · exact positiveChordBox1007_positive hxl hxu
    · exact positiveChordBox1008_positive hxl hxu
    · exact positiveChordBox1009_positive hxl hxu
    · exact positiveChordBox1010_positive hxl hxu
    · exact positiveChordBox1011_positive hxl hxu
    · exact positiveChordBox1012_positive hxl hxu
    · exact positiveChordBox1013_positive hxl hxu
    · exact positiveChordBox1014_positive hxl hxu
    · exact positiveChordBox1015_positive hxl hxu
    · exact positiveChordBox1016_positive hxl hxu
    · exact positiveChordBox1017_positive hxl hxu
    · exact positiveChordBox1018_positive hxl hxu
    · exact positiveChordBox1019_positive hxl hxu
    · exact positiveChordBox1020_positive hxl hxu
    · exact positiveChordBox1021_positive hxl hxu
    · exact positiveChordBox1022_positive hxl hxu
    · exact positiveChordBox1023_positive hxl hxu
    · exact positiveChordBox1024_positive hxl hxu
    · exact positiveChordBox1025_positive hxl hxu
    · exact positiveChordBox1026_positive hxl hxu
    · exact positiveChordBox1027_positive hxl hxu
    · exact positiveChordBox1028_positive hxl hxu
    · exact positiveChordBox1029_positive hxl hxu
    · exact positiveChordBox1030_positive hxl hxu
    · exact positiveChordBox1031_positive hxl hxu
    · exact positiveChordBox1032_positive hxl hxu
    · exact positiveChordBox1033_positive hxl hxu
    · exact positiveChordBox1034_positive hxl hxu
    · exact positiveChordBox1035_positive hxl hxu
    · exact positiveChordBox1036_positive hxl hxu
    · exact positiveChordBox1037_positive hxl hxu
    · exact positiveChordBox1038_positive hxl hxu
    · exact positiveChordBox1039_positive hxl hxu
    · exact positiveChordBox1040_positive hxl hxu
    · exact positiveChordBox1041_positive hxl hxu
    · exact positiveChordBox1042_positive hxl hxu
    · exact positiveChordBox1043_positive hxl hxu
    · exact positiveChordBox1044_positive hxl hxu
    · exact positiveChordBox1045_positive hxl hxu
    · exact positiveChordBox1046_positive hxl hxu
    · exact positiveChordBox1047_positive hxl hxu
    · exact positiveChordBox1048_positive hxl hxu
    · exact positiveChordBox1049_positive hxl hxu
    · exact positiveChordBox1050_positive hxl hxu
    · exact positiveChordBox1051_positive hxl hxu
    · exact positiveChordBox1052_positive hxl hxu
    · exact positiveChordBox1053_positive hxl hxu
    · exact positiveChordBox1054_positive hxl hxu
    · exact positiveChordBox1055_positive hxl hxu
    · exact positiveChordBox1056_positive hxl hxu
    · exact positiveChordBox1057_positive hxl hxu
    · exact positiveChordBox1058_positive hxl hxu
    · exact positiveChordBox1059_positive hxl hxu
    · exact positiveChordBox1060_positive hxl hxu
    · exact positiveChordBox1061_positive hxl hxu
    · exact positiveChordBox1062_positive hxl hxu
    · exact positiveChordBox1063_positive hxl hxu
    · exact positiveChordBox1064_positive hxl hxu
    · exact positiveChordBox1065_positive hxl hxu
    · exact positiveChordBox1066_positive hxl hxu
    · exact positiveChordBox1067_positive hxl hxu
    · exact positiveChordBox1068_positive hxl hxu
    · exact positiveChordBox1069_positive hxl hxu
    · exact positiveChordBox1070_positive hxl hxu
    · exact positiveChordBox1071_positive hxl hxu
    · exact positiveChordBox1072_positive hxl hxu
    · exact positiveChordBox1073_positive hxl hxu
    · exact positiveChordBox1074_positive hxl hxu
    · exact positiveChordBox1075_positive hxl hxu
    · exact positiveChordBox1076_positive hxl hxu
    · exact positiveChordBox1077_positive hxl hxu
    · exact positiveChordBox1078_positive hxl hxu
    · exact positiveChordBox1079_positive hxl hxu
    · exact positiveChordBox1080_positive hxl hxu
    · exact positiveChordBox1081_positive hxl hxu
    · exact positiveChordBox1082_positive hxl hxu
    · exact positiveChordBox1083_positive hxl hxu
    · exact positiveChordBox1084_positive hxl hxu
    · exact positiveChordBox1085_positive hxl hxu
    · exact positiveChordBox1086_positive hxl hxu
    · exact positiveChordBox1087_positive hxl hxu
    · exact positiveChordBox1088_positive hxl hxu
    · exact positiveChordBox1089_positive hxl hxu
    · exact positiveChordBox1090_positive hxl hxu
    · exact positiveChordBox1091_positive hxl hxu
    · exact positiveChordBox1092_positive hxl hxu
    · exact positiveChordBox1093_positive hxl hxu
    · exact positiveChordBox1094_positive hxl hxu
    · exact positiveChordBox1095_positive hxl hxu
    · exact positiveChordBox1096_positive hxl hxu
    · exact positiveChordBox1097_positive hxl hxu
    · exact positiveChordBox1098_positive hxl hxu
  · simpa only [positiveChordParameterBoundary, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using htl
  · simpa only [positiveChordParameterBoundary, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using htu

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actualPeriodAlong_positive_compact
