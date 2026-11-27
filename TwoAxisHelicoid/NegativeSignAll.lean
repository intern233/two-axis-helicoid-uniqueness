import TwoAxisHelicoid.FiniteIntervalChain
import TwoAxisHelicoid.NegativeChordBox1000
import TwoAxisHelicoid.NegativeChordBox1001
import TwoAxisHelicoid.NegativeChordBox1002
import TwoAxisHelicoid.NegativeChordBox1003
import TwoAxisHelicoid.NegativeChordBox1004
import TwoAxisHelicoid.NegativeChordBox1005
import TwoAxisHelicoid.NegativeChordBox1006
import TwoAxisHelicoid.NegativeChordBox1007
import TwoAxisHelicoid.NegativeChordBox1008
import TwoAxisHelicoid.NegativeChordBox1009
import TwoAxisHelicoid.NegativeChordBox1010
import TwoAxisHelicoid.NegativeChordBox1011
import TwoAxisHelicoid.NegativeChordBox1012
import TwoAxisHelicoid.NegativeChordBox1013
import TwoAxisHelicoid.NegativeChordBox1014
import TwoAxisHelicoid.NegativeChordBox1015
import TwoAxisHelicoid.NegativeChordBox1016
import TwoAxisHelicoid.NegativeChordBox1017
import TwoAxisHelicoid.NegativeChordBox1018
import TwoAxisHelicoid.NegativeChordBox1019
import TwoAxisHelicoid.NegativeChordBox1020
import TwoAxisHelicoid.NegativeChordBox1021
import TwoAxisHelicoid.NegativeChordBox1022
import TwoAxisHelicoid.NegativeChordBox1023
import TwoAxisHelicoid.NegativeChordBox1024
import TwoAxisHelicoid.NegativeChordBox1025
import TwoAxisHelicoid.NegativeChordBox1026
import TwoAxisHelicoid.NegativeChordBox1027
import TwoAxisHelicoid.NegativeChordBox1028
import TwoAxisHelicoid.NegativeChordBox1029
import TwoAxisHelicoid.NegativeChordBox1030
import TwoAxisHelicoid.NegativeChordBox1031
import TwoAxisHelicoid.NegativeChordBox1032
import TwoAxisHelicoid.NegativeChordBox1033
import TwoAxisHelicoid.NegativeChordBox1034
import TwoAxisHelicoid.NegativeChordBox1035
import TwoAxisHelicoid.NegativeChordBox1036
import TwoAxisHelicoid.NegativeChordBox1037
import TwoAxisHelicoid.NegativeChordBox1038
import TwoAxisHelicoid.NegativeChordBox1039
import TwoAxisHelicoid.NegativeChordBox1040
import TwoAxisHelicoid.NegativeChordBox1041
import TwoAxisHelicoid.NegativeChordBox1042
import TwoAxisHelicoid.NegativeChordBox1043
import TwoAxisHelicoid.NegativeChordBox1044
import TwoAxisHelicoid.NegativeChordBox1045
import TwoAxisHelicoid.NegativeChordBox1046
import TwoAxisHelicoid.NegativeChordBox1047
import TwoAxisHelicoid.NegativeChordBox1048
import TwoAxisHelicoid.NegativeChordBox1049
import TwoAxisHelicoid.NegativeChordBox1050
import TwoAxisHelicoid.NegativeChordBox1051
import TwoAxisHelicoid.NegativeChordBox1052
import TwoAxisHelicoid.NegativeChordBox1053
import TwoAxisHelicoid.NegativeChordBox1054
import TwoAxisHelicoid.NegativeChordBox1055
import TwoAxisHelicoid.NegativeChordBox1056
import TwoAxisHelicoid.NegativeChordBox1057
import TwoAxisHelicoid.NegativeChordBox1058
import TwoAxisHelicoid.NegativeChordBox1059
import TwoAxisHelicoid.NegativeChordBox1060
import TwoAxisHelicoid.NegativeChordBox1061
import TwoAxisHelicoid.NegativeChordBox1062
import TwoAxisHelicoid.NegativeChordBox1063
import TwoAxisHelicoid.NegativeChordBox1064
import TwoAxisHelicoid.NegativeChordBox1065
import TwoAxisHelicoid.NegativeChordBox1066
import TwoAxisHelicoid.NegativeChordBox1067
import TwoAxisHelicoid.NegativeChordBox1068
import TwoAxisHelicoid.NegativeChordBox1069

namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def negativeChordParameterBoundary : ℕ → ℚ := fun i => match i with
  | 0 => (9/10)
  | 1 => (577/640)
  | 2 => (289/320)
  | 3 => (579/640)
  | 4 => (29/32)
  | 5 => (581/640)
  | 6 => (291/320)
  | 7 => (583/640)
  | 8 => (73/80)
  | 9 => (117/128)
  | 10 => (293/320)
  | 11 => (147/160)
  | 12 => (59/64)
  | 13 => (37/40)
  | 14 => (297/320)
  | 15 => (149/160)
  | 16 => (299/320)
  | 17 => (15/16)
  | 18 => (301/320)
  | 19 => (151/160)
  | 20 => (303/320)
  | 21 => (19/20)
  | 22 => (61/64)
  | 23 => (153/160)
  | 24 => (307/320)
  | 25 => (77/80)
  | 26 => (309/320)
  | 27 => (31/32)
  | 28 => (39/40)
  | 29 => (157/160)
  | 30 => (79/80)
  | 31 => (159/160)
  | 32 => (1/1)
  | 33 => (161/160)
  | 34 => (81/80)
  | 35 => (163/160)
  | 36 => (41/40)
  | 37 => (33/32)
  | 38 => (83/80)
  | 39 => (167/160)
  | 40 => (21/20)
  | 41 => (169/160)
  | 42 => (17/16)
  | 43 => (171/160)
  | 44 => (43/40)
  | 45 => (87/80)
  | 46 => (11/10)
  | 47 => (89/80)
  | 48 => (9/8)
  | 49 => (91/80)
  | 50 => (23/20)
  | 51 => (93/80)
  | 52 => (47/40)
  | 53 => (19/16)
  | 54 => (6/5)
  | 55 => (97/80)
  | 56 => (49/40)
  | 57 => (99/80)
  | 58 => (5/4)
  | 59 => (101/80)
  | 60 => (51/40)
  | 61 => (103/80)
  | 62 => (13/10)
  | 63 => (21/16)
  | 64 => (53/40)
  | 65 => (107/80)
  | 66 => (27/20)
  | 67 => (109/80)
  | 68 => (11/8)
  | 69 => (111/80)
  | _ => (7/5)

theorem actualPeriodAlong_negative_compact {t : ℝ}
    (htl : ((9/10) : ℝ) ≤ t)
    (htu : t ≤ ((7/5) : ℝ)) :
    actualPeriodAlong t < (-1/25 : ℝ) := by
  apply predicate_on_interval_chain 69 (fun i => (negativeChordParameterBoundary i : ℝ))
    (fun x => actualPeriodAlong x < (-1/25 : ℝ))
  · intro i x hxl hxu
    fin_cases i
    · exact negativeChordBox1000_negative hxl hxu
    · exact negativeChordBox1001_negative hxl hxu
    · exact negativeChordBox1002_negative hxl hxu
    · exact negativeChordBox1003_negative hxl hxu
    · exact negativeChordBox1004_negative hxl hxu
    · exact negativeChordBox1005_negative hxl hxu
    · exact negativeChordBox1006_negative hxl hxu
    · exact negativeChordBox1007_negative hxl hxu
    · exact negativeChordBox1008_negative hxl hxu
    · exact negativeChordBox1009_negative hxl hxu
    · exact negativeChordBox1010_negative hxl hxu
    · exact negativeChordBox1011_negative hxl hxu
    · exact negativeChordBox1012_negative hxl hxu
    · exact negativeChordBox1013_negative hxl hxu
    · exact negativeChordBox1014_negative hxl hxu
    · exact negativeChordBox1015_negative hxl hxu
    · exact negativeChordBox1016_negative hxl hxu
    · exact negativeChordBox1017_negative hxl hxu
    · exact negativeChordBox1018_negative hxl hxu
    · exact negativeChordBox1019_negative hxl hxu
    · exact negativeChordBox1020_negative hxl hxu
    · exact negativeChordBox1021_negative hxl hxu
    · exact negativeChordBox1022_negative hxl hxu
    · exact negativeChordBox1023_negative hxl hxu
    · exact negativeChordBox1024_negative hxl hxu
    · exact negativeChordBox1025_negative hxl hxu
    · exact negativeChordBox1026_negative hxl hxu
    · exact negativeChordBox1027_negative hxl hxu
    · exact negativeChordBox1028_negative hxl hxu
    · exact negativeChordBox1029_negative hxl hxu
    · exact negativeChordBox1030_negative hxl hxu
    · exact negativeChordBox1031_negative hxl hxu
    · exact negativeChordBox1032_negative hxl hxu
    · exact negativeChordBox1033_negative hxl hxu
    · exact negativeChordBox1034_negative hxl hxu
    · exact negativeChordBox1035_negative hxl hxu
    · exact negativeChordBox1036_negative hxl hxu
    · exact negativeChordBox1037_negative hxl hxu
    · exact negativeChordBox1038_negative hxl hxu
    · exact negativeChordBox1039_negative hxl hxu
    · exact negativeChordBox1040_negative hxl hxu
    · exact negativeChordBox1041_negative hxl hxu
    · exact negativeChordBox1042_negative hxl hxu
    · exact negativeChordBox1043_negative hxl hxu
    · exact negativeChordBox1044_negative hxl hxu
    · exact negativeChordBox1045_negative hxl hxu
    · exact negativeChordBox1046_negative hxl hxu
    · exact negativeChordBox1047_negative hxl hxu
    · exact negativeChordBox1048_negative hxl hxu
    · exact negativeChordBox1049_negative hxl hxu
    · exact negativeChordBox1050_negative hxl hxu
    · exact negativeChordBox1051_negative hxl hxu
    · exact negativeChordBox1052_negative hxl hxu
    · exact negativeChordBox1053_negative hxl hxu
    · exact negativeChordBox1054_negative hxl hxu
    · exact negativeChordBox1055_negative hxl hxu
    · exact negativeChordBox1056_negative hxl hxu
    · exact negativeChordBox1057_negative hxl hxu
    · exact negativeChordBox1058_negative hxl hxu
    · exact negativeChordBox1059_negative hxl hxu
    · exact negativeChordBox1060_negative hxl hxu
    · exact negativeChordBox1061_negative hxl hxu
    · exact negativeChordBox1062_negative hxl hxu
    · exact negativeChordBox1063_negative hxl hxu
    · exact negativeChordBox1064_negative hxl hxu
    · exact negativeChordBox1065_negative hxl hxu
    · exact negativeChordBox1066_negative hxl hxu
    · exact negativeChordBox1067_negative hxl hxu
    · exact negativeChordBox1068_negative hxl hxu
    · exact negativeChordBox1069_negative hxl hxu
  · simpa only [negativeChordParameterBoundary, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using htl
  · simpa only [negativeChordParameterBoundary, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using htu

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actualPeriodAlong_negative_compact
