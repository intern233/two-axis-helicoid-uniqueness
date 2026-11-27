import TwoAxisHelicoid.TraceDataSlopingSpatialMesh
import TwoAxisHelicoid.TraceDataSlopingFluxCover

namespace TwoAxisHelicoid.TraceData
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

private theorem slopingFirstBlock0Part0 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (0/1) (1/8) ⟨(-145/64),(-17/64),(-557/2048),(-3/64),(-557/2048),(0/1)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell000 (0/1) (1/64) (-67/32) (-31/64) (by decide +kernel) slopingFluxCell000_checked (by decide +kernel)) (.cell slopingFluxCell001 (1/64) (1/32) (-135/64) (-29/64) (by decide +kernel) slopingFluxCell001_checked (by decide +kernel))) (.join (.cell slopingFluxCell002 (1/32) (3/64) (-137/64) (-27/64) (by decide +kernel) slopingFluxCell002_checked (by decide +kernel)) (.cell slopingFluxCell003 (3/64) (1/16) (-69/32) (-25/64) (by decide +kernel) slopingFluxCell003_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell004 (1/16) (5/64) (-35/16) (-23/64) (by decide +kernel) slopingFluxCell004_checked (by decide +kernel)) (.cell slopingFluxCell005 (5/64) (3/32) (-71/32) (-21/64) (by decide +kernel) slopingFluxCell005_checked (by decide +kernel))) (.join (.cell slopingFluxCell006 (3/32) (7/64) (-143/64) (-19/64) (by decide +kernel) slopingFluxCell006_checked (by decide +kernel)) (.cell slopingFluxCell007 (7/64) (1/8) (-145/64) (-17/64) (by decide +kernel) slopingFluxCell007_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingFirstBlock0Part1 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (1/8) (3/16) ⟨(-19/8),(-3/32),(-299/2048),(-41/4096),(-299/2048),(0/1)⟩ :=
  .relabel (.join (.join (.cell slopingFluxCell008 (1/8) (9/64) (-147/64) (-7/32) (by decide +kernel) slopingFluxCell008_checked (by decide +kernel)) (.cell slopingFluxCell009 (9/64) (5/32) (-149/64) (-3/16) (by decide +kernel) slopingFluxCell009_checked (by decide +kernel))) (.join (.cell slopingFluxCell010 (5/32) (11/64) (-75/32) (-9/64) (by decide +kernel) slopingFluxCell010_checked (by decide +kernel)) (.cell slopingFluxCell011 (11/64) (3/16) (-19/8) (-3/32) (by decide +kernel) slopingFluxCell011_checked (by decide +kernel)))) (by decide +kernel)

theorem slopingFirstSpan01 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (0/1) (3/16) ⟨(-19/8),(-3/32),(-107/256),(-233/4096),(-107/256),(0/1)⟩ :=
  .relabel (.join slopingFirstBlock0Part0 slopingFirstBlock0Part1) (by decide +kernel)

private theorem slopingFirstBlock1Part0 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (3/16) (1/4) ⟨(-57/32),(-9/16),(-455/4096),(-161/4096),(-455/4096),(0/1)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell012 (3/16) (25/128) (-113/64) (-11/16) (by decide +kernel) slopingFluxCell012_checked (by decide +kernel)) (.cell slopingFluxCell013 (25/128) (13/64) (-113/64) (-43/64) (by decide +kernel) slopingFluxCell013_checked (by decide +kernel))) (.join (.cell slopingFluxCell014 (13/64) (27/128) (-57/32) (-21/32) (by decide +kernel) slopingFluxCell014_checked (by decide +kernel)) (.cell slopingFluxCell015 (27/128) (7/32) (-57/32) (-41/64) (by decide +kernel) slopingFluxCell015_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell016 (7/32) (29/128) (-57/32) (-5/8) (by decide +kernel) slopingFluxCell016_checked (by decide +kernel)) (.cell slopingFluxCell017 (29/128) (15/64) (-57/32) (-39/64) (by decide +kernel) slopingFluxCell017_checked (by decide +kernel))) (.join (.cell slopingFluxCell018 (15/64) (31/128) (-57/32) (-37/64) (by decide +kernel) slopingFluxCell018_checked (by decide +kernel)) (.cell slopingFluxCell019 (31/128) (1/4) (-57/32) (-9/16) (by decide +kernel) slopingFluxCell019_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingFirstBlock1Part1 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (1/4) (5/16) ⟨(-115/64),(-25/64),(-115/1024),(-15/512),(-115/1024),(0/1)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell020 (1/4) (33/128) (-115/64) (-35/64) (by decide +kernel) slopingFluxCell020_checked (by decide +kernel)) (.cell slopingFluxCell021 (33/128) (17/64) (-115/64) (-17/32) (by decide +kernel) slopingFluxCell021_checked (by decide +kernel))) (.join (.cell slopingFluxCell022 (17/64) (35/128) (-115/64) (-1/2) (by decide +kernel) slopingFluxCell022_checked (by decide +kernel)) (.cell slopingFluxCell023 (35/128) (9/32) (-115/64) (-31/64) (by decide +kernel) slopingFluxCell023_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell024 (9/32) (37/128) (-115/64) (-29/64) (by decide +kernel) slopingFluxCell024_checked (by decide +kernel)) (.cell slopingFluxCell025 (37/128) (19/64) (-115/64) (-7/16) (by decide +kernel) slopingFluxCell025_checked (by decide +kernel))) (.join (.cell slopingFluxCell026 (19/64) (39/128) (-115/64) (-13/32) (by decide +kernel) slopingFluxCell026_checked (by decide +kernel)) (.cell slopingFluxCell027 (39/128) (5/16) (-115/64) (-25/64) (by decide +kernel) slopingFluxCell027_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingFirstBlock1Part2 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (5/16) (3/8) ⟨(-115/64),(-5/32),(-913/8192),(-67/4096),(-913/8192),(0/1)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell028 (5/16) (41/128) (-115/64) (-23/64) (by decide +kernel) slopingFluxCell028_checked (by decide +kernel)) (.cell slopingFluxCell029 (41/128) (21/64) (-115/64) (-21/64) (by decide +kernel) slopingFluxCell029_checked (by decide +kernel))) (.join (.cell slopingFluxCell030 (21/64) (43/128) (-57/32) (-5/16) (by decide +kernel) slopingFluxCell030_checked (by decide +kernel)) (.cell slopingFluxCell031 (43/128) (11/32) (-57/32) (-9/32) (by decide +kernel) slopingFluxCell031_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell032 (11/32) (45/128) (-57/32) (-1/4) (by decide +kernel) slopingFluxCell032_checked (by decide +kernel)) (.cell slopingFluxCell033 (45/128) (23/64) (-57/32) (-7/32) (by decide +kernel) slopingFluxCell033_checked (by decide +kernel))) (.join (.cell slopingFluxCell034 (23/64) (47/128) (-57/32) (-3/16) (by decide +kernel) slopingFluxCell034_checked (by decide +kernel)) (.cell slopingFluxCell035 (47/128) (3/8) (-113/64) (-5/32) (by decide +kernel) slopingFluxCell035_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingFirstBlock1Part3 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (3/8) (51/128) ⟨(-113/64),(-3/64),(-169/4096),(-15/8192),(-169/4096),(0/1)⟩ :=
  .relabel (.join (.cell slopingFluxCell036 (3/8) (49/128) (-113/64) (-7/64) (by decide +kernel) slopingFluxCell036_checked (by decide +kernel)) (.join (.cell slopingFluxCell037 (49/128) (25/64) (-113/64) (-5/64) (by decide +kernel) slopingFluxCell037_checked (by decide +kernel)) (.cell slopingFluxCell038 (25/64) (51/128) (-7/4) (-3/64) (by decide +kernel) slopingFluxCell038_checked (by decide +kernel)))) (by decide +kernel)

theorem slopingFirstSpan12 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (3/16) (51/128) ⟨(-115/64),(-3/64),(-3081/8192),(-711/8192),(-3081/8192),(0/1)⟩ :=
  .relabel (.join (.join slopingFirstBlock1Part0 slopingFirstBlock1Part1) (.join slopingFirstBlock1Part2 slopingFirstBlock1Part3)) (by decide +kernel)

private theorem slopingFirstBlock2Part0 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (51/128) (59/128) ⟨(-7/4),(19/64),(-877/8192),(9/1024),(-877/8192),(9/1024)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell039 (51/128) (13/32) (-7/4) (0/1) (by decide +kernel) slopingFluxCell039_checked (by decide +kernel)) (.cell slopingFluxCell040 (13/32) (53/128) (-111/64) (1/32) (by decide +kernel) slopingFluxCell040_checked (by decide +kernel))) (.join (.cell slopingFluxCell041 (53/128) (27/64) (-111/64) (5/64) (by decide +kernel) slopingFluxCell041_checked (by decide +kernel)) (.cell slopingFluxCell042 (27/64) (55/128) (-55/32) (7/64) (by decide +kernel) slopingFluxCell042_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell043 (55/128) (7/16) (-109/64) (5/32) (by decide +kernel) slopingFluxCell043_checked (by decide +kernel)) (.cell slopingFluxCell044 (7/16) (57/128) (-109/64) (13/64) (by decide +kernel) slopingFluxCell044_checked (by decide +kernel))) (.join (.cell slopingFluxCell045 (57/128) (29/64) (-27/16) (1/4) (by decide +kernel) slopingFluxCell045_checked (by decide +kernel)) (.cell slopingFluxCell046 (29/64) (59/128) (-107/64) (19/64) (by decide +kernel) slopingFluxCell046_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingFirstBlock2Part1 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (59/128) (67/128) ⟨(-53/32),(47/64),(-823/8192),(271/8192),(-823/8192),(271/8192)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell047 (59/128) (15/32) (-53/32) (11/32) (by decide +kernel) slopingFluxCell047_checked (by decide +kernel)) (.cell slopingFluxCell048 (15/32) (61/128) (-105/64) (25/64) (by decide +kernel) slopingFluxCell048_checked (by decide +kernel))) (.join (.cell slopingFluxCell049 (61/128) (31/64) (-13/8) (7/16) (by decide +kernel) slopingFluxCell049_checked (by decide +kernel)) (.cell slopingFluxCell050 (31/64) (63/128) (-103/64) (1/2) (by decide +kernel) slopingFluxCell050_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell051 (63/128) (1/2) (-51/32) (35/64) (by decide +kernel) slopingFluxCell051_checked (by decide +kernel)) (.cell slopingFluxCell052 (1/2) (65/128) (-51/32) (39/64) (by decide +kernel) slopingFluxCell052_checked (by decide +kernel))) (.join (.cell slopingFluxCell053 (65/128) (33/64) (-101/64) (43/64) (by decide +kernel) slopingFluxCell053_checked (by decide +kernel)) (.cell slopingFluxCell054 (33/64) (67/128) (-25/16) (47/64) (by decide +kernel) slopingFluxCell054_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingFirstBlock2Part2 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (67/128) (17/32) ⟨(-99/64),(51/64),(-99/8192),(51/8192),(-99/8192),(51/8192)⟩ :=
  .relabel (.cell slopingFluxCell055 (67/128) (17/32) (-99/64) (51/64) (by decide +kernel) slopingFluxCell055_checked (by decide +kernel)) (by decide +kernel)

theorem slopingFirstSpan23 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (51/128) (17/32) ⟨(-7/4),(51/64),(-1799/8192),(197/4096),(-1799/8192),(197/4096)⟩ :=
  .relabel (.join slopingFirstBlock2Part0 (.join slopingFirstBlock2Part1 slopingFirstBlock2Part2)) (by decide +kernel)

private theorem slopingFirstBlock3Part0 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (17/32) (19/32) ⟨(-49/32),(11/8),(-747/8192),(571/8192),(-747/8192),(571/8192)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell056 (17/32) (69/128) (-49/32) (7/8) (by decide +kernel) slopingFluxCell056_checked (by decide +kernel)) (.cell slopingFluxCell057 (69/128) (35/64) (-3/2) (15/16) (by decide +kernel) slopingFluxCell057_checked (by decide +kernel))) (.join (.cell slopingFluxCell058 (35/64) (71/128) (-95/64) (1/1) (by decide +kernel) slopingFluxCell058_checked (by decide +kernel)) (.cell slopingFluxCell059 (71/128) (9/16) (-47/32) (69/64) (by decide +kernel) slopingFluxCell059_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell060 (9/16) (73/128) (-93/64) (73/64) (by decide +kernel) slopingFluxCell060_checked (by decide +kernel)) (.cell slopingFluxCell061 (73/128) (37/64) (-23/16) (39/32) (by decide +kernel) slopingFluxCell061_checked (by decide +kernel))) (.join (.cell slopingFluxCell062 (37/64) (75/128) (-45/32) (83/64) (by decide +kernel) slopingFluxCell062_checked (by decide +kernel)) (.cell slopingFluxCell063 (75/128) (19/32) (-89/64) (11/8) (by decide +kernel) slopingFluxCell063_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingFirstBlock3Part1 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (19/32) (81/128) ⟨(-11/8),(49/32),(-17/512),(365/8192),(-17/512),(365/8192)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell064 (19/32) (77/128) (-11/8) (93/64) (by decide +kernel) slopingFluxCell064_checked (by decide +kernel)) (.cell slopingFluxCell065 (77/128) (39/64) (-43/32) (49/32) (by decide +kernel) slopingFluxCell065_checked (by decide +kernel))) (.join (.cell slopingFluxCell066 (39/64) (157/256) (-9/16) (53/64) (by decide +kernel) slopingFluxCell066_checked (by decide +kernel)) (.cell slopingFluxCell067 (157/256) (79/128) (-35/64) (55/64) (by decide +kernel) slopingFluxCell067_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell068 (79/128) (159/256) (-33/64) (57/64) (by decide +kernel) slopingFluxCell068_checked (by decide +kernel)) (.cell slopingFluxCell069 (159/256) (5/8) (-1/2) (59/64) (by decide +kernel) slopingFluxCell069_checked (by decide +kernel))) (.join (.cell slopingFluxCell070 (5/8) (161/256) (-31/64) (61/64) (by decide +kernel) slopingFluxCell070_checked (by decide +kernel)) (.cell slopingFluxCell071 (161/256) (81/128) (-29/64) (63/64) (by decide +kernel) slopingFluxCell071_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingFirstBlock3Part2 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (81/128) (85/128) ⟨(-7/16),(81/64),(-189/16384),(293/8192),(-189/16384),(293/8192)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell072 (81/128) (163/256) (-7/16) (65/64) (by decide +kernel) slopingFluxCell072_checked (by decide +kernel)) (.cell slopingFluxCell073 (163/256) (41/64) (-27/64) (17/16) (by decide +kernel) slopingFluxCell073_checked (by decide +kernel))) (.join (.cell slopingFluxCell074 (41/64) (165/256) (-13/32) (35/32) (by decide +kernel) slopingFluxCell074_checked (by decide +kernel)) (.cell slopingFluxCell075 (165/256) (83/128) (-3/8) (9/8) (by decide +kernel) slopingFluxCell075_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell076 (83/128) (167/256) (-23/64) (37/32) (by decide +kernel) slopingFluxCell076_checked (by decide +kernel)) (.cell slopingFluxCell077 (167/256) (21/32) (-11/32) (77/64) (by decide +kernel) slopingFluxCell077_checked (by decide +kernel))) (.join (.cell slopingFluxCell078 (21/32) (169/256) (-5/16) (79/64) (by decide +kernel) slopingFluxCell078_checked (by decide +kernel)) (.cell slopingFluxCell079 (169/256) (85/128) (-19/64) (81/64) (by decide +kernel) slopingFluxCell079_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingFirstBlock3Part3 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (85/128) (89/128) ⟨(-17/64),(25/16),(-25/4096),(183/4096),(-25/4096),(183/4096)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell080 (85/128) (171/256) (-17/64) (83/64) (by decide +kernel) slopingFluxCell080_checked (by decide +kernel)) (.cell slopingFluxCell081 (171/256) (43/64) (-1/4) (43/32) (by decide +kernel) slopingFluxCell081_checked (by decide +kernel))) (.join (.cell slopingFluxCell082 (43/64) (173/256) (-15/64) (11/8) (by decide +kernel) slopingFluxCell082_checked (by decide +kernel)) (.cell slopingFluxCell083 (173/256) (87/128) (-13/64) (45/32) (by decide +kernel) slopingFluxCell083_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell084 (87/128) (175/256) (-3/16) (93/64) (by decide +kernel) slopingFluxCell084_checked (by decide +kernel)) (.cell slopingFluxCell085 (175/256) (11/16) (-5/32) (95/64) (by decide +kernel) slopingFluxCell085_checked (by decide +kernel))) (.join (.cell slopingFluxCell086 (11/16) (177/256) (-9/64) (97/64) (by decide +kernel) slopingFluxCell086_checked (by decide +kernel)) (.cell slopingFluxCell087 (177/256) (89/128) (-1/8) (25/16) (by decide +kernel) slopingFluxCell087_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingFirstBlock3Part4 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (89/128) (183/256) ⟨(-3/32),(7/4),(-17/16384),(535/16384),(-17/16384),(535/16384)⟩ :=
  .relabel (.join (.join (.cell slopingFluxCell088 (89/128) (179/256) (-3/32) (51/32) (by decide +kernel) slopingFluxCell088_checked (by decide +kernel)) (.cell slopingFluxCell089 (179/256) (45/64) (-5/64) (105/64) (by decide +kernel) slopingFluxCell089_checked (by decide +kernel))) (.join (.cell slopingFluxCell090 (45/64) (181/256) (-3/64) (107/64) (by decide +kernel) slopingFluxCell090_checked (by decide +kernel)) (.join (.cell slopingFluxCell091 (181/256) (91/128) (-1/32) (109/64) (by decide +kernel) slopingFluxCell091_checked (by decide +kernel)) (.cell slopingFluxCell092 (91/128) (183/256) (-1/64) (7/4) (by decide +kernel) slopingFluxCell092_checked (by decide +kernel))))) (by decide +kernel)

theorem slopingFirstSpan34 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (17/32) (183/256) ⟨(-49/32),(7/4),(-293/2048),(3725/16384),(-293/2048),(3725/16384)⟩ :=
  .relabel (.join (.join slopingFirstBlock3Part0 slopingFirstBlock3Part1) (.join slopingFirstBlock3Part2 (.join slopingFirstBlock3Part3 slopingFirstBlock3Part4))) (by decide +kernel)

private theorem slopingFirstBlock4Part0 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (183/256) (191/256) ⟨(1/64),(131/64),(23/8192),(981/16384),(0/1),(981/16384)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell093 (183/256) (23/32) (1/64) (57/32) (by decide +kernel) slopingFluxCell093_checked (by decide +kernel)) (.cell slopingFluxCell094 (23/32) (185/256) (1/32) (117/64) (by decide +kernel) slopingFluxCell094_checked (by decide +kernel))) (.join (.cell slopingFluxCell095 (185/256) (93/128) (1/16) (119/64) (by decide +kernel) slopingFluxCell095_checked (by decide +kernel)) (.cell slopingFluxCell096 (93/128) (187/256) (5/64) (121/64) (by decide +kernel) slopingFluxCell096_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell097 (187/256) (47/64) (3/32) (31/16) (by decide +kernel) slopingFluxCell097_checked (by decide +kernel)) (.cell slopingFluxCell098 (47/64) (189/256) (1/8) (63/32) (by decide +kernel) slopingFluxCell098_checked (by decide +kernel))) (.join (.cell slopingFluxCell099 (189/256) (95/128) (9/64) (129/64) (by decide +kernel) slopingFluxCell099_checked (by decide +kernel)) (.cell slopingFluxCell100 (95/128) (191/256) (11/64) (131/64) (by decide +kernel) slopingFluxCell100_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingFirstBlock4Part1 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (191/256) (199/256) ⟨(3/16),(75/32),(135/16384),(71/1024),(0/1),(71/1024)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell101 (191/256) (3/4) (3/16) (67/32) (by decide +kernel) slopingFluxCell101_checked (by decide +kernel)) (.cell slopingFluxCell102 (3/4) (193/256) (13/64) (17/8) (by decide +kernel) slopingFluxCell102_checked (by decide +kernel))) (.join (.cell slopingFluxCell103 (193/256) (97/128) (15/64) (69/32) (by decide +kernel) slopingFluxCell103_checked (by decide +kernel)) (.cell slopingFluxCell104 (97/128) (195/256) (1/4) (141/64) (by decide +kernel) slopingFluxCell104_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell105 (195/256) (49/64) (9/32) (143/64) (by decide +kernel) slopingFluxCell105_checked (by decide +kernel)) (.cell slopingFluxCell106 (49/64) (197/256) (19/64) (73/32) (by decide +kernel) slopingFluxCell106_checked (by decide +kernel))) (.join (.cell slopingFluxCell107 (197/256) (99/128) (5/16) (37/16) (by decide +kernel) slopingFluxCell107_checked (by decide +kernel)) (.cell slopingFluxCell108 (99/128) (199/256) (11/32) (75/32) (by decide +kernel) slopingFluxCell108_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingFirstBlock4Part2 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (199/256) (207/256) ⟨(23/64),(169/64),(219/16384),(1287/16384),(0/1),(1287/16384)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell109 (199/256) (25/32) (23/64) (153/64) (by decide +kernel) slopingFluxCell109_checked (by decide +kernel)) (.cell slopingFluxCell110 (25/32) (201/256) (3/8) (155/64) (by decide +kernel) slopingFluxCell110_checked (by decide +kernel))) (.join (.cell slopingFluxCell111 (201/256) (101/128) (25/64) (157/64) (by decide +kernel) slopingFluxCell111_checked (by decide +kernel)) (.cell slopingFluxCell112 (101/128) (203/256) (27/64) (5/2) (by decide +kernel) slopingFluxCell112_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell113 (203/256) (51/64) (7/16) (81/32) (by decide +kernel) slopingFluxCell113_checked (by decide +kernel)) (.cell slopingFluxCell114 (51/64) (205/256) (29/64) (41/16) (by decide +kernel) slopingFluxCell114_checked (by decide +kernel))) (.join (.cell slopingFluxCell115 (205/256) (103/128) (31/64) (167/64) (by decide +kernel) slopingFluxCell115_checked (by decide +kernel)) (.cell slopingFluxCell116 (103/128) (207/256) (1/2) (169/64) (by decide +kernel) slopingFluxCell116_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingFirstBlock4Part3 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (207/256) (215/256) ⟨(33/64),(187/64),(73/4096),(1433/16384),(0/1),(1433/16384)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell117 (207/256) (13/16) (33/64) (171/64) (by decide +kernel) slopingFluxCell117_checked (by decide +kernel)) (.cell slopingFluxCell118 (13/16) (209/256) (17/32) (173/64) (by decide +kernel) slopingFluxCell118_checked (by decide +kernel))) (.join (.cell slopingFluxCell119 (209/256) (105/128) (35/64) (11/4) (by decide +kernel) slopingFluxCell119_checked (by decide +kernel)) (.cell slopingFluxCell120 (105/128) (211/256) (9/16) (89/32) (by decide +kernel) slopingFluxCell120_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell121 (211/256) (53/64) (37/64) (45/16) (by decide +kernel) slopingFluxCell121_checked (by decide +kernel)) (.cell slopingFluxCell122 (53/64) (213/256) (19/32) (183/64) (by decide +kernel) slopingFluxCell122_checked (by decide +kernel))) (.join (.cell slopingFluxCell123 (213/256) (107/128) (39/64) (185/64) (by decide +kernel) slopingFluxCell123_checked (by decide +kernel)) (.cell slopingFluxCell124 (107/128) (215/256) (5/8) (187/64) (by decide +kernel) slopingFluxCell124_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingFirstBlock4Part4 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (215/256) (223/256) ⟨(41/64),(51/16),(87/4096),(197/2048),(0/1),(197/2048)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell125 (215/256) (27/32) (41/64) (95/32) (by decide +kernel) slopingFluxCell125_checked (by decide +kernel)) (.cell slopingFluxCell126 (27/32) (217/256) (21/32) (3/1) (by decide +kernel) slopingFluxCell126_checked (by decide +kernel))) (.join (.cell slopingFluxCell127 (217/256) (109/128) (21/32) (97/32) (by decide +kernel) slopingFluxCell127_checked (by decide +kernel)) (.cell slopingFluxCell128 (109/128) (219/256) (43/64) (49/16) (by decide +kernel) slopingFluxCell128_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell129 (219/256) (55/64) (11/16) (99/32) (by decide +kernel) slopingFluxCell129_checked (by decide +kernel)) (.cell slopingFluxCell130 (55/64) (221/256) (45/64) (25/8) (by decide +kernel) slopingFluxCell130_checked (by decide +kernel))) (.join (.cell slopingFluxCell131 (221/256) (111/128) (45/64) (101/32) (by decide +kernel) slopingFluxCell131_checked (by decide +kernel)) (.cell slopingFluxCell132 (111/128) (223/256) (23/32) (51/16) (by decide +kernel) slopingFluxCell132_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingFirstBlock4Part5 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (223/256) (225/256) ⟨(47/64),(209/64),(47/8192),(13/512),(0/1),(13/512)⟩ :=
  .relabel (.join (.cell slopingFluxCell133 (223/256) (7/8) (47/64) (207/64) (by decide +kernel) slopingFluxCell133_checked (by decide +kernel)) (.cell slopingFluxCell134 (7/8) (225/256) (47/64) (209/64) (by decide +kernel) slopingFluxCell134_checked (by decide +kernel))) (by decide +kernel)

theorem slopingFirstSpan45 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (183/256) (225/256) ⟨(1/64),(209/64),(567/8192),(6829/16384),(0/1),(6829/16384)⟩ :=
  .relabel (.join (.join slopingFirstBlock4Part0 (.join slopingFirstBlock4Part1 slopingFirstBlock4Part2)) (.join slopingFirstBlock4Part3 (.join slopingFirstBlock4Part4 slopingFirstBlock4Part5))) (by decide +kernel)

private theorem slopingFirstBlock5Part0 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (225/256) (233/256) ⟨(3/4),(223/64),(99/4096),(1735/16384),(0/1),(1735/16384)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell135 (225/256) (113/128) (3/4) (105/32) (by decide +kernel) slopingFluxCell135_checked (by decide +kernel)) (.cell slopingFluxCell136 (113/128) (227/256) (3/4) (53/16) (by decide +kernel) slopingFluxCell136_checked (by decide +kernel))) (.join (.cell slopingFluxCell137 (227/256) (57/64) (49/64) (107/32) (by decide +kernel) slopingFluxCell137_checked (by decide +kernel)) (.cell slopingFluxCell138 (57/64) (229/256) (49/64) (27/8) (by decide +kernel) slopingFluxCell138_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell139 (229/256) (115/128) (25/32) (109/32) (by decide +kernel) slopingFluxCell139_checked (by decide +kernel)) (.cell slopingFluxCell140 (115/128) (231/256) (25/32) (55/16) (by decide +kernel) slopingFluxCell140_checked (by decide +kernel))) (.join (.cell slopingFluxCell141 (231/256) (29/32) (51/64) (111/32) (by decide +kernel) slopingFluxCell141_checked (by decide +kernel)) (.cell slopingFluxCell142 (29/32) (233/256) (51/64) (223/64) (by decide +kernel) slopingFluxCell142_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingFirstBlock5Part1 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (233/256) (237/256) ⟨(3/2),(23/8),(779/32768),(363/8192),(0/1),(363/8192)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell143 (233/256) (467/512) (3/2) (179/64) (by decide +kernel) slopingFluxCell143_checked (by decide +kernel)) (.cell slopingFluxCell144 (467/512) (117/128) (97/64) (45/16) (by decide +kernel) slopingFluxCell144_checked (by decide +kernel))) (.join (.cell slopingFluxCell145 (117/128) (469/512) (97/64) (181/64) (by decide +kernel) slopingFluxCell145_checked (by decide +kernel)) (.cell slopingFluxCell146 (469/512) (235/256) (97/64) (181/64) (by decide +kernel) slopingFluxCell146_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell147 (235/256) (471/512) (49/32) (91/32) (by decide +kernel) slopingFluxCell147_checked (by decide +kernel)) (.cell slopingFluxCell148 (471/512) (59/64) (49/32) (91/32) (by decide +kernel) slopingFluxCell148_checked (by decide +kernel))) (.join (.cell slopingFluxCell149 (59/64) (473/512) (49/32) (183/64) (by decide +kernel) slopingFluxCell149_checked (by decide +kernel)) (.cell slopingFluxCell150 (473/512) (237/256) (49/32) (23/8) (by decide +kernel) slopingFluxCell150_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingFirstBlock5Part2 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (237/256) (241/256) ⟨(99/64),(47/16),(199/8192),(93/2048),(0/1),(93/2048)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell151 (237/256) (475/512) (99/64) (23/8) (by decide +kernel) slopingFluxCell151_checked (by decide +kernel)) (.cell slopingFluxCell152 (475/512) (119/128) (99/64) (185/64) (by decide +kernel) slopingFluxCell152_checked (by decide +kernel))) (.join (.cell slopingFluxCell153 (119/128) (477/512) (99/64) (185/64) (by decide +kernel) slopingFluxCell153_checked (by decide +kernel)) (.cell slopingFluxCell154 (477/512) (239/256) (99/64) (93/32) (by decide +kernel) slopingFluxCell154_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell155 (239/256) (479/512) (25/16) (93/32) (by decide +kernel) slopingFluxCell155_checked (by decide +kernel)) (.cell slopingFluxCell156 (479/512) (15/16) (25/16) (187/64) (by decide +kernel) slopingFluxCell156_checked (by decide +kernel))) (.join (.cell slopingFluxCell157 (15/16) (481/512) (25/16) (187/64) (by decide +kernel) slopingFluxCell157_checked (by decide +kernel)) (.cell slopingFluxCell158 (481/512) (241/256) (25/16) (47/16) (by decide +kernel) slopingFluxCell158_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingFirstBlock5Part3 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (241/256) (245/256) ⟨(25/16),(3/1),(807/32768),(95/2048),(0/1),(95/2048)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell159 (241/256) (483/512) (25/16) (47/16) (by decide +kernel) slopingFluxCell159_checked (by decide +kernel)) (.cell slopingFluxCell160 (483/512) (121/128) (101/64) (189/64) (by decide +kernel) slopingFluxCell160_checked (by decide +kernel))) (.join (.cell slopingFluxCell161 (121/128) (485/512) (101/64) (189/64) (by decide +kernel) slopingFluxCell161_checked (by decide +kernel)) (.cell slopingFluxCell162 (485/512) (243/256) (101/64) (95/32) (by decide +kernel) slopingFluxCell162_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell163 (243/256) (487/512) (101/64) (95/32) (by decide +kernel) slopingFluxCell163_checked (by decide +kernel)) (.cell slopingFluxCell164 (487/512) (61/64) (101/64) (191/64) (by decide +kernel) slopingFluxCell164_checked (by decide +kernel))) (.join (.cell slopingFluxCell165 (61/64) (489/512) (101/64) (191/64) (by decide +kernel) slopingFluxCell165_checked (by decide +kernel)) (.cell slopingFluxCell166 (489/512) (245/256) (101/64) (3/1) (by decide +kernel) slopingFluxCell166_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingFirstBlock5Part4 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (245/256) (249/256) ⟨(101/64),(97/32),(815/32768),(1545/32768),(0/1),(1545/32768)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell167 (245/256) (491/512) (101/64) (3/1) (by decide +kernel) slopingFluxCell167_checked (by decide +kernel)) (.cell slopingFluxCell168 (491/512) (123/128) (51/32) (3/1) (by decide +kernel) slopingFluxCell168_checked (by decide +kernel))) (.join (.cell slopingFluxCell169 (123/128) (493/512) (51/32) (193/64) (by decide +kernel) slopingFluxCell169_checked (by decide +kernel)) (.cell slopingFluxCell170 (493/512) (247/256) (51/32) (193/64) (by decide +kernel) slopingFluxCell170_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell171 (247/256) (495/512) (51/32) (193/64) (by decide +kernel) slopingFluxCell171_checked (by decide +kernel)) (.cell slopingFluxCell172 (495/512) (31/32) (51/32) (97/32) (by decide +kernel) slopingFluxCell172_checked (by decide +kernel))) (.join (.cell slopingFluxCell173 (31/32) (497/512) (51/32) (97/32) (by decide +kernel) slopingFluxCell173_checked (by decide +kernel)) (.cell slopingFluxCell174 (497/512) (249/256) (51/32) (97/32) (by decide +kernel) slopingFluxCell174_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingFirstBlock5Part5 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (249/256) (253/256) ⟨(51/32),(197/64),(51/2048),(783/16384),(0/1),(783/16384)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell175 (249/256) (499/512) (51/32) (195/64) (by decide +kernel) slopingFluxCell175_checked (by decide +kernel)) (.cell slopingFluxCell176 (499/512) (125/128) (51/32) (195/64) (by decide +kernel) slopingFluxCell176_checked (by decide +kernel))) (.join (.cell slopingFluxCell177 (125/128) (501/512) (51/32) (195/64) (by decide +kernel) slopingFluxCell177_checked (by decide +kernel)) (.cell slopingFluxCell178 (501/512) (251/256) (51/32) (49/16) (by decide +kernel) slopingFluxCell178_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell179 (251/256) (503/512) (51/32) (49/16) (by decide +kernel) slopingFluxCell179_checked (by decide +kernel)) (.cell slopingFluxCell180 (503/512) (63/64) (51/32) (49/16) (by decide +kernel) slopingFluxCell180_checked (by decide +kernel))) (.join (.cell slopingFluxCell181 (63/64) (505/512) (51/32) (49/16) (by decide +kernel) slopingFluxCell181_checked (by decide +kernel)) (.cell slopingFluxCell182 (505/512) (253/256) (51/32) (197/64) (by decide +kernel) slopingFluxCell182_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingFirstBlock5Part6 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (253/256) (1/1) ⟨(101/64),(99/32),(607/32768),(1183/32768),(0/1),(1183/32768)⟩ :=
  .relabel (.join (.join (.cell slopingFluxCell183 (253/256) (507/512) (51/32) (197/64) (by decide +kernel) slopingFluxCell183_checked (by decide +kernel)) (.join (.cell slopingFluxCell184 (507/512) (127/128) (101/64) (197/64) (by decide +kernel) slopingFluxCell184_checked (by decide +kernel)) (.cell slopingFluxCell185 (127/128) (509/512) (101/64) (197/64) (by decide +kernel) slopingFluxCell185_checked (by decide +kernel)))) (.join (.cell slopingFluxCell186 (509/512) (255/256) (101/64) (197/64) (by decide +kernel) slopingFluxCell186_checked (by decide +kernel)) (.join (.cell slopingFluxCell187 (255/256) (511/512) (101/64) (197/64) (by decide +kernel) slopingFluxCell187_checked (by decide +kernel)) (.cell slopingFluxCell188 (511/512) (1/1) (101/64) (99/32) (by decide +kernel) slopingFluxCell188_checked (by decide +kernel))))) (by decide +kernel)

theorem slopingFirstSpan56 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (225/256) (1/1) ⟨(3/4),(223/64),(1353/8192),(191/512),(0/1),(191/512)⟩ :=
  .relabel (.join (.join slopingFirstBlock5Part0 (.join slopingFirstBlock5Part1 slopingFirstBlock5Part2)) (.join (.join slopingFirstBlock5Part3 slopingFirstBlock5Part4) (.join slopingFirstBlock5Part5 slopingFirstBlock5Part6))) (by decide +kernel)

theorem slopingFirstSpan02 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (0/1) (51/128) ⟨(-19/8),(-3/64),(-6505/8192),(-1177/8192),(-6505/8192),(0/1)⟩ :=
  .relabel (.join slopingFirstSpan01 slopingFirstSpan12) (by decide +kernel)

theorem slopingFirstSpan15 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (3/16) (225/256) ⟨(-115/64),(209/64),(-5485/8192),(155/256),(-1513/2048),(5671/8192)⟩ :=
  .relabel (.join (.join slopingFirstSpan12 slopingFirstSpan23) (.join slopingFirstSpan34 slopingFirstSpan45)) (by decide +kernel)

theorem slopingFirstSpan46 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (183/256) (1/1) ⟨(1/64),(223/64),(15/64),(12941/16384),(0/1),(12941/16384)⟩ :=
  .relabel (.join slopingFirstSpan45 slopingFirstSpan56) (by decide +kernel)

theorem slopingFirstSpan26 :
    CheckedSlopingScalar true slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (51/128) (1/1) ⟨(-7/4),(223/64),(-1051/8192),(8727/8192),(-2971/8192),(8727/8192)⟩ :=
  .relabel (.join (.join slopingFirstSpan23 slopingFirstSpan34) (.join slopingFirstSpan45 slopingFirstSpan56)) (by decide +kernel)

private theorem slopingSecondBlock0Part0 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (0/1) (1/8) ⟨(-49/64),(101/64),(-19/256),(617/4096),(-19/256),(617/4096)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell000 (0/1) (1/64) (-49/64) (27/32) (by decide +kernel) slopingFluxCell000_checked (by decide +kernel)) (.cell slopingFluxCell001 (1/64) (1/32) (-23/32) (15/16) (by decide +kernel) slopingFluxCell001_checked (by decide +kernel))) (.join (.cell slopingFluxCell002 (1/32) (3/64) (-43/64) (67/64) (by decide +kernel) slopingFluxCell002_checked (by decide +kernel)) (.cell slopingFluxCell003 (3/64) (1/16) (-39/64) (37/32) (by decide +kernel) slopingFluxCell003_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell004 (1/16) (5/64) (-9/16) (5/4) (by decide +kernel) slopingFluxCell004_checked (by decide +kernel)) (.cell slopingFluxCell005 (5/64) (3/32) (-33/64) (87/64) (by decide +kernel) slopingFluxCell005_checked (by decide +kernel))) (.join (.cell slopingFluxCell006 (3/32) (7/64) (-15/32) (47/32) (by decide +kernel) slopingFluxCell006_checked (by decide +kernel)) (.cell slopingFluxCell007 (7/64) (1/8) (-7/16) (101/64) (by decide +kernel) slopingFluxCell007_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingSecondBlock0Part1 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (1/8) (3/16) ⟨(-25/64),(129/64),(-21/1024),(237/2048),(-21/1024),(237/2048)⟩ :=
  .relabel (.join (.join (.cell slopingFluxCell008 (1/8) (9/64) (-25/64) (27/16) (by decide +kernel) slopingFluxCell008_checked (by decide +kernel)) (.cell slopingFluxCell009 (9/64) (5/32) (-11/32) (115/64) (by decide +kernel) slopingFluxCell009_checked (by decide +kernel))) (.join (.cell slopingFluxCell010 (5/32) (11/64) (-5/16) (61/32) (by decide +kernel) slopingFluxCell010_checked (by decide +kernel)) (.cell slopingFluxCell011 (11/64) (3/16) (-17/64) (129/64) (by decide +kernel) slopingFluxCell011_checked (by decide +kernel)))) (by decide +kernel)

theorem slopingSecondSpan01 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (0/1) (3/16) ⟨(-49/64),(129/64),(-97/1024),(1091/4096),(-97/1024),(1091/4096)⟩ :=
  .relabel (.join slopingSecondBlock0Part0 slopingSecondBlock0Part1) (by decide +kernel)

private theorem slopingSecondBlock1Part0 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (3/16) (1/4) ⟨(25/64),(29/16),(63/2048),(841/8192),(0/1),(841/8192)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell012 (3/16) (25/128) (25/64) (47/32) (by decide +kernel) slopingFluxCell012_checked (by decide +kernel)) (.cell slopingFluxCell013 (25/128) (13/64) (27/64) (97/64) (by decide +kernel) slopingFluxCell013_checked (by decide +kernel))) (.join (.cell slopingFluxCell014 (13/64) (27/128) (29/64) (25/16) (by decide +kernel) slopingFluxCell014_checked (by decide +kernel)) (.cell slopingFluxCell015 (27/128) (7/32) (31/64) (13/8) (by decide +kernel) slopingFluxCell015_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell016 (7/32) (29/128) (1/2) (107/64) (by decide +kernel) slopingFluxCell016_checked (by decide +kernel)) (.cell slopingFluxCell017 (29/128) (15/64) (17/32) (55/32) (by decide +kernel) slopingFluxCell017_checked (by decide +kernel))) (.join (.cell slopingFluxCell018 (15/64) (31/128) (9/16) (113/64) (by decide +kernel) slopingFluxCell018_checked (by decide +kernel)) (.cell slopingFluxCell019 (31/128) (1/4) (19/32) (29/16) (by decide +kernel) slopingFluxCell019_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingSecondBlock1Part1 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (1/4) (5/16) ⟨(39/64),(141/64),(45/1024),(1037/8192),(0/1),(1037/8192)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell020 (1/4) (33/128) (39/64) (119/64) (by decide +kernel) slopingFluxCell020_checked (by decide +kernel)) (.cell slopingFluxCell021 (33/128) (17/64) (41/64) (61/32) (by decide +kernel) slopingFluxCell021_checked (by decide +kernel))) (.join (.cell slopingFluxCell022 (17/64) (35/128) (43/64) (125/64) (by decide +kernel) slopingFluxCell022_checked (by decide +kernel)) (.cell slopingFluxCell023 (35/128) (9/32) (11/16) (2/1) (by decide +kernel) slopingFluxCell023_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell024 (9/32) (37/128) (23/32) (131/64) (by decide +kernel) slopingFluxCell024_checked (by decide +kernel)) (.cell slopingFluxCell025 (37/128) (19/64) (47/64) (67/32) (by decide +kernel) slopingFluxCell025_checked (by decide +kernel))) (.join (.cell slopingFluxCell026 (19/64) (39/128) (49/64) (137/64) (by decide +kernel) slopingFluxCell026_checked (by decide +kernel)) (.cell slopingFluxCell027 (39/128) (5/16) (51/64) (141/64) (by decide +kernel) slopingFluxCell027_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingSecondBlock1Part2 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (5/16) (3/8) ⟨(13/16),(83/32),(57/1024),(1237/8192),(0/1),(1237/8192)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell028 (5/16) (41/128) (13/16) (9/4) (by decide +kernel) slopingFluxCell028_checked (by decide +kernel)) (.cell slopingFluxCell029 (41/128) (21/64) (27/32) (147/64) (by decide +kernel) slopingFluxCell029_checked (by decide +kernel))) (.join (.cell slopingFluxCell030 (21/64) (43/128) (55/64) (75/32) (by decide +kernel) slopingFluxCell030_checked (by decide +kernel)) (.cell slopingFluxCell031 (43/128) (11/32) (7/8) (153/64) (by decide +kernel) slopingFluxCell031_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell032 (11/32) (45/128) (29/32) (39/16) (by decide +kernel) slopingFluxCell032_checked (by decide +kernel)) (.cell slopingFluxCell033 (45/128) (23/64) (59/64) (159/64) (by decide +kernel) slopingFluxCell033_checked (by decide +kernel))) (.join (.cell slopingFluxCell034 (23/64) (47/128) (15/16) (81/32) (by decide +kernel) slopingFluxCell034_checked (by decide +kernel)) (.cell slopingFluxCell035 (47/128) (3/8) (31/32) (83/32) (by decide +kernel) slopingFluxCell035_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingSecondBlock1Part3 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (3/8) (51/128) ⟨(63/64),(175/64),(3/128),(129/2048),(0/1),(129/2048)⟩ :=
  .relabel (.join (.cell slopingFluxCell036 (3/8) (49/128) (63/64) (169/64) (by decide +kernel) slopingFluxCell036_checked (by decide +kernel)) (.join (.cell slopingFluxCell037 (49/128) (25/64) (1/1) (43/16) (by decide +kernel) slopingFluxCell037_checked (by decide +kernel)) (.cell slopingFluxCell038 (25/64) (51/128) (65/64) (175/64) (by decide +kernel) slopingFluxCell038_checked (by decide +kernel)))) (by decide +kernel)

theorem slopingSecondSpan12 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (3/16) (51/128) ⟨(25/64),(175/64),(315/2048),(3631/8192),(0/1),(3631/8192)⟩ :=
  .relabel (.join (.join slopingSecondBlock1Part0 slopingSecondBlock1Part1) (.join slopingSecondBlock1Part2 slopingSecondBlock1Part3)) (by decide +kernel)

private theorem slopingSecondBlock2Part0 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (51/128) (59/128) ⟨(33/32),(199/64),(139/2048),(377/2048),(0/1),(377/2048)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell039 (51/128) (13/32) (33/32) (89/32) (by decide +kernel) slopingFluxCell039_checked (by decide +kernel)) (.cell slopingFluxCell040 (13/32) (53/128) (67/64) (181/64) (by decide +kernel) slopingFluxCell040_checked (by decide +kernel))) (.join (.cell slopingFluxCell041 (53/128) (27/64) (17/16) (23/8) (by decide +kernel) slopingFluxCell041_checked (by decide +kernel)) (.cell slopingFluxCell042 (27/64) (55/128) (69/64) (187/64) (by decide +kernel) slopingFluxCell042_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell043 (55/128) (7/16) (35/32) (95/32) (by decide +kernel) slopingFluxCell043_checked (by decide +kernel)) (.cell slopingFluxCell044 (7/16) (57/128) (71/64) (193/64) (by decide +kernel) slopingFluxCell044_checked (by decide +kernel))) (.join (.cell slopingFluxCell045 (57/128) (29/64) (9/8) (49/16) (by decide +kernel) slopingFluxCell045_checked (by decide +kernel)) (.cell slopingFluxCell046 (29/64) (59/128) (73/64) (199/64) (by decide +kernel) slopingFluxCell046_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingSecondBlock2Part1 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (59/128) (67/128) ⟨(73/64),(221/64),(149/2048),(1691/8192),(0/1),(1691/8192)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell047 (59/128) (15/32) (73/64) (201/64) (by decide +kernel) slopingFluxCell047_checked (by decide +kernel)) (.cell slopingFluxCell048 (15/32) (61/128) (37/32) (51/16) (by decide +kernel) slopingFluxCell048_checked (by decide +kernel))) (.join (.cell slopingFluxCell049 (61/128) (31/64) (37/32) (207/64) (by decide +kernel) slopingFluxCell049_checked (by decide +kernel)) (.cell slopingFluxCell050 (31/64) (63/128) (75/64) (105/32) (by decide +kernel) slopingFluxCell050_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell051 (63/128) (1/2) (75/64) (213/64) (by decide +kernel) slopingFluxCell051_checked (by decide +kernel)) (.cell slopingFluxCell052 (1/2) (65/128) (75/64) (27/8) (by decide +kernel) slopingFluxCell052_checked (by decide +kernel))) (.join (.cell slopingFluxCell053 (65/128) (33/64) (75/64) (219/64) (by decide +kernel) slopingFluxCell053_checked (by decide +kernel)) (.cell slopingFluxCell054 (33/64) (67/128) (75/64) (221/64) (by decide +kernel) slopingFluxCell054_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingSecondBlock2Part2 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (67/128) (17/32) ⟨(37/32),(7/2),(37/4096),(7/256),(0/1),(7/256)⟩ :=
  .relabel (.cell slopingFluxCell055 (67/128) (17/32) (37/32) (7/2) (by decide +kernel) slopingFluxCell055_checked (by decide +kernel)) (by decide +kernel)

theorem slopingSecondSpan23 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (51/128) (17/32) ⟨(33/32),(7/2),(613/4096),(3423/8192),(0/1),(3423/8192)⟩ :=
  .relabel (.join slopingSecondBlock2Part0 (.join slopingSecondBlock2Part1 slopingSecondBlock2Part2)) (by decide +kernel)

private theorem slopingSecondBlock3Part0 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (17/32) (19/32) ⟨(17/16),(245/64),(285/4096),(59/256),(0/1),(59/256)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell056 (17/32) (69/128) (37/32) (227/64) (by decide +kernel) slopingFluxCell056_checked (by decide +kernel)) (.cell slopingFluxCell057 (69/128) (35/64) (73/64) (115/32) (by decide +kernel) slopingFluxCell057_checked (by decide +kernel))) (.join (.cell slopingFluxCell058 (35/64) (71/128) (73/64) (29/8) (by decide +kernel) slopingFluxCell058_checked (by decide +kernel)) (.cell slopingFluxCell059 (71/128) (9/16) (9/8) (235/64) (by decide +kernel) slopingFluxCell059_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell060 (9/16) (73/128) (71/64) (237/64) (by decide +kernel) slopingFluxCell060_checked (by decide +kernel)) (.cell slopingFluxCell061 (73/128) (37/64) (35/32) (15/4) (by decide +kernel) slopingFluxCell061_checked (by decide +kernel))) (.join (.cell slopingFluxCell062 (37/64) (75/128) (69/64) (121/32) (by decide +kernel) slopingFluxCell062_checked (by decide +kernel)) (.cell slopingFluxCell063 (75/128) (19/32) (17/16) (245/64) (by decide +kernel) slopingFluxCell063_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingSecondBlock3Part1 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (19/32) (81/128) ⟨(65/64),(249/64),(467/8192),(2207/16384),(0/1),(2207/16384)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell064 (19/32) (77/128) (33/32) (247/64) (by decide +kernel) slopingFluxCell064_checked (by decide +kernel)) (.cell slopingFluxCell065 (77/128) (39/64) (65/64) (249/64) (by decide +kernel) slopingFluxCell065_checked (by decide +kernel))) (.join (.cell slopingFluxCell066 (39/64) (157/256) (113/64) (201/64) (by decide +kernel) slopingFluxCell066_checked (by decide +kernel)) (.cell slopingFluxCell067 (157/256) (79/128) (113/64) (101/32) (by decide +kernel) slopingFluxCell067_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell068 (79/128) (159/256) (7/4) (101/32) (by decide +kernel) slopingFluxCell068_checked (by decide +kernel)) (.cell slopingFluxCell069 (159/256) (5/8) (7/4) (203/64) (by decide +kernel) slopingFluxCell069_checked (by decide +kernel))) (.join (.cell slopingFluxCell070 (5/8) (161/256) (111/64) (203/64) (by decide +kernel) slopingFluxCell070_checked (by decide +kernel)) (.cell slopingFluxCell071 (161/256) (81/128) (111/64) (51/16) (by decide +kernel) slopingFluxCell071_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingSecondBlock3Part2 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (81/128) (85/128) ⟨(53/32),(103/32),(867/16384),(1641/16384),(0/1),(1641/16384)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell072 (81/128) (163/256) (111/64) (51/16) (by decide +kernel) slopingFluxCell072_checked (by decide +kernel)) (.cell slopingFluxCell073 (163/256) (41/64) (55/32) (51/16) (by decide +kernel) slopingFluxCell073_checked (by decide +kernel))) (.join (.cell slopingFluxCell074 (41/64) (165/256) (109/64) (205/64) (by decide +kernel) slopingFluxCell074_checked (by decide +kernel)) (.cell slopingFluxCell075 (165/256) (83/128) (109/64) (205/64) (by decide +kernel) slopingFluxCell075_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell076 (83/128) (167/256) (27/16) (205/64) (by decide +kernel) slopingFluxCell076_checked (by decide +kernel)) (.cell slopingFluxCell077 (167/256) (21/32) (107/64) (103/32) (by decide +kernel) slopingFluxCell077_checked (by decide +kernel))) (.join (.cell slopingFluxCell078 (21/32) (169/256) (107/64) (103/32) (by decide +kernel) slopingFluxCell078_checked (by decide +kernel)) (.cell slopingFluxCell079 (169/256) (85/128) (53/32) (103/32) (by decide +kernel) slopingFluxCell079_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingSecondBlock3Part3 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (85/128) (89/128) ⟨(99/64),(103/32),(409/8192),(103/1024),(0/1),(103/1024)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell080 (85/128) (171/256) (105/64) (103/32) (by decide +kernel) slopingFluxCell080_checked (by decide +kernel)) (.cell slopingFluxCell081 (171/256) (43/64) (13/8) (103/32) (by decide +kernel) slopingFluxCell081_checked (by decide +kernel))) (.join (.cell slopingFluxCell082 (43/64) (173/256) (13/8) (103/32) (by decide +kernel) slopingFluxCell082_checked (by decide +kernel)) (.cell slopingFluxCell083 (173/256) (87/128) (103/64) (103/32) (by decide +kernel) slopingFluxCell083_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell084 (87/128) (175/256) (51/32) (103/32) (by decide +kernel) slopingFluxCell084_checked (by decide +kernel)) (.cell slopingFluxCell085 (175/256) (11/16) (101/64) (103/32) (by decide +kernel) slopingFluxCell085_checked (by decide +kernel))) (.join (.cell slopingFluxCell086 (11/16) (177/256) (25/16) (103/32) (by decide +kernel) slopingFluxCell086_checked (by decide +kernel)) (.cell slopingFluxCell087 (177/256) (89/128) (99/64) (103/32) (by decide +kernel) slopingFluxCell087_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingSecondBlock3Part4 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (89/128) (183/256) ⟨(93/64),(103/32),(119/4096),(1029/16384),(0/1),(1029/16384)⟩ :=
  .relabel (.join (.join (.cell slopingFluxCell088 (89/128) (179/256) (49/32) (103/32) (by decide +kernel) slopingFluxCell088_checked (by decide +kernel)) (.cell slopingFluxCell089 (179/256) (45/64) (3/2) (103/32) (by decide +kernel) slopingFluxCell089_checked (by decide +kernel))) (.join (.cell slopingFluxCell090 (45/64) (181/256) (95/64) (103/32) (by decide +kernel) slopingFluxCell090_checked (by decide +kernel)) (.join (.cell slopingFluxCell091 (181/256) (91/128) (47/32) (103/32) (by decide +kernel) slopingFluxCell091_checked (by decide +kernel)) (.cell slopingFluxCell092 (91/128) (183/256) (93/64) (205/64) (by decide +kernel) slopingFluxCell092_checked (by decide +kernel))))) (by decide +kernel)

theorem slopingSecondSpan34 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (17/32) (183/256) ⟨(65/64),(249/64),(4235/16384),(10301/16384),(0/1),(10301/16384)⟩ :=
  .relabel (.join (.join slopingSecondBlock3Part0 slopingSecondBlock3Part1) (.join slopingSecondBlock3Part2 (.join slopingSecondBlock3Part3 slopingSecondBlock3Part4))) (by decide +kernel)

private theorem slopingSecondBlock4Part0 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (183/256) (191/256) ⟨(81/64),(205/64),(693/16384),(407/4096),(0/1),(407/4096)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell093 (183/256) (23/32) (23/16) (205/64) (by decide +kernel) slopingFluxCell093_checked (by decide +kernel)) (.cell slopingFluxCell094 (23/32) (185/256) (45/32) (205/64) (by decide +kernel) slopingFluxCell094_checked (by decide +kernel))) (.join (.cell slopingFluxCell095 (185/256) (93/128) (89/64) (51/16) (by decide +kernel) slopingFluxCell095_checked (by decide +kernel)) (.cell slopingFluxCell096 (93/128) (187/256) (87/64) (51/16) (by decide +kernel) slopingFluxCell096_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell097 (187/256) (47/64) (43/32) (203/64) (by decide +kernel) slopingFluxCell097_checked (by decide +kernel)) (.cell slopingFluxCell098 (47/64) (189/256) (85/64) (203/64) (by decide +kernel) slopingFluxCell098_checked (by decide +kernel))) (.join (.cell slopingFluxCell099 (189/256) (95/128) (83/64) (101/32) (by decide +kernel) slopingFluxCell099_checked (by decide +kernel)) (.cell slopingFluxCell100 (95/128) (191/256) (81/64) (101/32) (by decide +kernel) slopingFluxCell100_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingSecondBlock4Part1 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (191/256) (199/256) ⟨(67/64),(201/64),(589/16384),(1591/16384),(0/1),(1591/16384)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell101 (191/256) (3/4) (5/4) (201/64) (by decide +kernel) slopingFluxCell101_checked (by decide +kernel)) (.cell slopingFluxCell102 (3/4) (193/256) (39/32) (201/64) (by decide +kernel) slopingFluxCell102_checked (by decide +kernel))) (.join (.cell slopingFluxCell103 (193/256) (97/128) (19/16) (25/8) (by decide +kernel) slopingFluxCell103_checked (by decide +kernel)) (.cell slopingFluxCell104 (97/128) (195/256) (75/64) (199/64) (by decide +kernel) slopingFluxCell104_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell105 (195/256) (49/64) (73/64) (199/64) (by decide +kernel) slopingFluxCell105_checked (by decide +kernel)) (.cell slopingFluxCell106 (49/64) (197/256) (71/64) (99/32) (by decide +kernel) slopingFluxCell106_checked (by decide +kernel))) (.join (.cell slopingFluxCell107 (197/256) (99/128) (69/64) (197/64) (by decide +kernel) slopingFluxCell107_checked (by decide +kernel)) (.cell slopingFluxCell108 (99/128) (199/256) (67/64) (49/16) (by decide +kernel) slopingFluxCell108_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingSecondBlock4Part2 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (199/256) (207/256) ⟨(51/64),(195/64),(467/16384),(383/4096),(0/1),(383/4096)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell109 (199/256) (25/32) (33/32) (195/64) (by decide +kernel) slopingFluxCell109_checked (by decide +kernel)) (.cell slopingFluxCell110 (25/32) (201/256) (1/1) (97/32) (by decide +kernel) slopingFluxCell110_checked (by decide +kernel))) (.join (.cell slopingFluxCell111 (201/256) (101/128) (31/32) (193/64) (by decide +kernel) slopingFluxCell111_checked (by decide +kernel)) (.cell slopingFluxCell112 (101/128) (203/256) (59/64) (3/1) (by decide +kernel) slopingFluxCell112_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell113 (203/256) (51/64) (57/64) (191/64) (by decide +kernel) slopingFluxCell113_checked (by decide +kernel)) (.cell slopingFluxCell114 (51/64) (205/256) (55/64) (95/32) (by decide +kernel) slopingFluxCell114_checked (by decide +kernel))) (.join (.cell slopingFluxCell115 (205/256) (103/128) (53/64) (189/64) (by decide +kernel) slopingFluxCell115_checked (by decide +kernel)) (.cell slopingFluxCell116 (103/128) (207/256) (51/64) (47/16) (by decide +kernel) slopingFluxCell116_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingSecondBlock4Part3 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (207/256) (215/256) ⟨(31/64),(187/64),(5/256),(731/8192),(0/1),(731/8192)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell117 (207/256) (13/16) (49/64) (187/64) (by decide +kernel) slopingFluxCell117_checked (by decide +kernel)) (.cell slopingFluxCell118 (13/16) (209/256) (23/32) (93/32) (by decide +kernel) slopingFluxCell118_checked (by decide +kernel))) (.join (.cell slopingFluxCell119 (209/256) (105/128) (11/16) (185/64) (by decide +kernel) slopingFluxCell119_checked (by decide +kernel)) (.cell slopingFluxCell120 (105/128) (211/256) (41/64) (183/64) (by decide +kernel) slopingFluxCell120_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell121 (211/256) (53/64) (39/64) (91/32) (by decide +kernel) slopingFluxCell121_checked (by decide +kernel)) (.cell slopingFluxCell122 (53/64) (213/256) (9/16) (181/64) (by decide +kernel) slopingFluxCell122_checked (by decide +kernel))) (.join (.cell slopingFluxCell123 (213/256) (107/128) (17/32) (45/16) (by decide +kernel) slopingFluxCell123_checked (by decide +kernel)) (.cell slopingFluxCell124 (107/128) (215/256) (31/64) (89/32) (by decide +kernel) slopingFluxCell124_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingSecondBlock4Part4 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (215/256) (223/256) ⟨(9/64),(177/64),(37/4096),(43/512),(0/1),(43/512)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell125 (215/256) (27/32) (7/16) (177/64) (by decide +kernel) slopingFluxCell125_checked (by decide +kernel)) (.cell slopingFluxCell126 (27/32) (217/256) (13/32) (11/4) (by decide +kernel) slopingFluxCell126_checked (by decide +kernel))) (.join (.cell slopingFluxCell127 (217/256) (109/128) (23/64) (87/32) (by decide +kernel) slopingFluxCell127_checked (by decide +kernel)) (.cell slopingFluxCell128 (109/128) (219/256) (5/16) (173/64) (by decide +kernel) slopingFluxCell128_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell129 (219/256) (55/64) (17/64) (171/64) (by decide +kernel) slopingFluxCell129_checked (by decide +kernel)) (.cell slopingFluxCell130 (55/64) (221/256) (7/32) (85/32) (by decide +kernel) slopingFluxCell130_checked (by decide +kernel))) (.join (.cell slopingFluxCell131 (221/256) (111/128) (11/64) (21/8) (by decide +kernel) slopingFluxCell131_checked (by decide +kernel)) (.cell slopingFluxCell132 (111/128) (223/256) (9/64) (167/64) (by decide +kernel) slopingFluxCell132_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingSecondBlock4Part5 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (223/256) (225/256) ⟨(3/64),(165/64),(9/16384),(329/16384),(0/1),(329/16384)⟩ :=
  .relabel (.join (.cell slopingFluxCell133 (223/256) (7/8) (3/32) (165/64) (by decide +kernel) slopingFluxCell133_checked (by decide +kernel)) (.cell slopingFluxCell134 (7/8) (225/256) (3/64) (41/16) (by decide +kernel) slopingFluxCell134_checked (by decide +kernel))) (by decide +kernel)

theorem slopingSecondSpan45 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (183/256) (225/256) ⟨(3/64),(205/64),(1113/8192),(3959/8192),(0/1),(3959/8192)⟩ :=
  .relabel (.join (.join slopingSecondBlock4Part0 (.join slopingSecondBlock4Part1 slopingSecondBlock4Part2)) (.join slopingSecondBlock4Part3 (.join slopingSecondBlock4Part4 slopingSecondBlock4Part5))) (by decide +kernel)

private theorem slopingSecondBlock5Part0 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (225/256) (233/256) ⟨(-11/32),(81/32),(-91/16384),(1249/16384),(-91/16384),(1249/16384)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell135 (225/256) (113/128) (0/1) (81/32) (by decide +kernel) slopingFluxCell135_checked (by decide +kernel)) (.cell slopingFluxCell136 (113/128) (227/256) (-1/16) (5/2) (by decide +kernel) slopingFluxCell136_checked (by decide +kernel))) (.join (.cell slopingFluxCell137 (227/256) (57/64) (-7/64) (159/64) (by decide +kernel) slopingFluxCell137_checked (by decide +kernel)) (.cell slopingFluxCell138 (57/64) (229/256) (-5/32) (157/64) (by decide +kernel) slopingFluxCell138_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell139 (229/256) (115/128) (-13/64) (155/64) (by decide +kernel) slopingFluxCell139_checked (by decide +kernel)) (.cell slopingFluxCell140 (115/128) (231/256) (-1/4) (77/32) (by decide +kernel) slopingFluxCell140_checked (by decide +kernel))) (.join (.cell slopingFluxCell141 (231/256) (29/32) (-19/64) (19/8) (by decide +kernel) slopingFluxCell141_checked (by decide +kernel)) (.cell slopingFluxCell142 (29/32) (233/256) (-11/32) (75/32) (by decide +kernel) slopingFluxCell142_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingSecondBlock5Part1 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (233/256) (237/256) ⟨(5/32),(103/64),(123/32768),(795/32768),(0/1),(795/32768)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell143 (233/256) (467/512) (5/16) (103/64) (by decide +kernel) slopingFluxCell143_checked (by decide +kernel)) (.cell slopingFluxCell144 (467/512) (117/128) (19/64) (51/32) (by decide +kernel) slopingFluxCell144_checked (by decide +kernel))) (.join (.cell slopingFluxCell145 (117/128) (469/512) (9/32) (101/64) (by decide +kernel) slopingFluxCell145_checked (by decide +kernel)) (.cell slopingFluxCell146 (469/512) (235/256) (1/4) (25/16) (by decide +kernel) slopingFluxCell146_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell147 (235/256) (471/512) (15/64) (99/64) (by decide +kernel) slopingFluxCell147_checked (by decide +kernel)) (.cell slopingFluxCell148 (471/512) (59/64) (13/64) (49/32) (by decide +kernel) slopingFluxCell148_checked (by decide +kernel))) (.join (.cell slopingFluxCell149 (59/64) (473/512) (3/16) (97/64) (by decide +kernel) slopingFluxCell149_checked (by decide +kernel)) (.cell slopingFluxCell150 (473/512) (237/256) (5/32) (95/64) (by decide +kernel) slopingFluxCell150_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingSecondBlock5Part2 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (237/256) (241/256) ⟨(-1/32),(47/32),(7/8192),(721/32768),(-1/16384),(721/32768)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell151 (237/256) (475/512) (9/64) (47/32) (by decide +kernel) slopingFluxCell151_checked (by decide +kernel)) (.cell slopingFluxCell152 (475/512) (119/128) (7/64) (93/64) (by decide +kernel) slopingFluxCell152_checked (by decide +kernel))) (.join (.cell slopingFluxCell153 (119/128) (477/512) (3/32) (23/16) (by decide +kernel) slopingFluxCell153_checked (by decide +kernel)) (.cell slopingFluxCell154 (477/512) (239/256) (1/16) (91/64) (by decide +kernel) slopingFluxCell154_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell155 (239/256) (479/512) (3/64) (45/32) (by decide +kernel) slopingFluxCell155_checked (by decide +kernel)) (.cell slopingFluxCell156 (479/512) (15/16) (1/64) (11/8) (by decide +kernel) slopingFluxCell156_checked (by decide +kernel))) (.join (.cell slopingFluxCell157 (15/16) (481/512) (0/1) (87/64) (by decide +kernel) slopingFluxCell157_checked (by decide +kernel)) (.cell slopingFluxCell158 (481/512) (241/256) (-1/32) (43/32) (by decide +kernel) slopingFluxCell158_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingSecondBlock5Part3 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (241/256) (245/256) ⟨(-7/32),(85/64),(-17/8192),(645/32768),(-17/8192),(645/32768)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell159 (241/256) (483/512) (-3/64) (85/64) (by decide +kernel) slopingFluxCell159_checked (by decide +kernel)) (.cell slopingFluxCell160 (483/512) (121/128) (-5/64) (21/16) (by decide +kernel) slopingFluxCell160_checked (by decide +kernel))) (.join (.cell slopingFluxCell161 (121/128) (485/512) (-3/32) (41/32) (by decide +kernel) slopingFluxCell161_checked (by decide +kernel)) (.cell slopingFluxCell162 (485/512) (243/256) (-1/8) (81/64) (by decide +kernel) slopingFluxCell162_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell163 (243/256) (487/512) (-9/64) (5/4) (by decide +kernel) slopingFluxCell163_checked (by decide +kernel)) (.cell slopingFluxCell164 (487/512) (61/64) (-11/64) (79/64) (by decide +kernel) slopingFluxCell164_checked (by decide +kernel))) (.join (.cell slopingFluxCell165 (61/64) (489/512) (-3/16) (39/32) (by decide +kernel) slopingFluxCell165_checked (by decide +kernel)) (.cell slopingFluxCell166 (489/512) (245/256) (-7/32) (19/16) (by decide +kernel) slopingFluxCell166_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingSecondBlock5Part4 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (245/256) (249/256) ⟨(-13/32),(75/64),(-41/8192),(71/4096),(-41/8192),(71/4096)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell167 (245/256) (491/512) (-15/64) (75/64) (by decide +kernel) slopingFluxCell167_checked (by decide +kernel)) (.cell slopingFluxCell168 (491/512) (123/128) (-17/64) (37/32) (by decide +kernel) slopingFluxCell168_checked (by decide +kernel))) (.join (.cell slopingFluxCell169 (123/128) (493/512) (-9/32) (73/64) (by decide +kernel) slopingFluxCell169_checked (by decide +kernel)) (.cell slopingFluxCell170 (493/512) (247/256) (-5/16) (9/8) (by decide +kernel) slopingFluxCell170_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell171 (247/256) (495/512) (-21/64) (35/32) (by decide +kernel) slopingFluxCell171_checked (by decide +kernel)) (.cell slopingFluxCell172 (495/512) (31/32) (-23/64) (69/64) (by decide +kernel) slopingFluxCell172_checked (by decide +kernel))) (.join (.cell slopingFluxCell173 (31/32) (497/512) (-3/8) (17/16) (by decide +kernel) slopingFluxCell173_checked (by decide +kernel)) (.cell slopingFluxCell174 (497/512) (249/256) (-13/32) (67/64) (by decide +kernel) slopingFluxCell174_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingSecondBlock5Part5 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (249/256) (253/256) ⟨(-19/32),(65/64),(-33/4096),(61/4096),(-33/4096),(61/4096)⟩ :=
  .relabel (.join (.join (.join (.cell slopingFluxCell175 (249/256) (499/512) (-7/16) (65/64) (by decide +kernel) slopingFluxCell175_checked (by decide +kernel)) (.cell slopingFluxCell176 (499/512) (125/128) (-29/64) (1/1) (by decide +kernel) slopingFluxCell176_checked (by decide +kernel))) (.join (.cell slopingFluxCell177 (125/128) (501/512) (-31/64) (63/64) (by decide +kernel) slopingFluxCell177_checked (by decide +kernel)) (.cell slopingFluxCell178 (501/512) (251/256) (-1/2) (31/32) (by decide +kernel) slopingFluxCell178_checked (by decide +kernel)))) (.join (.join (.cell slopingFluxCell179 (251/256) (503/512) (-17/32) (15/16) (by decide +kernel) slopingFluxCell179_checked (by decide +kernel)) (.cell slopingFluxCell180 (503/512) (63/64) (-35/64) (59/64) (by decide +kernel) slopingFluxCell180_checked (by decide +kernel))) (.join (.cell slopingFluxCell181 (63/64) (505/512) (-37/64) (29/32) (by decide +kernel) slopingFluxCell181_checked (by decide +kernel)) (.cell slopingFluxCell182 (505/512) (253/256) (-19/32) (57/64) (by decide +kernel) slopingFluxCell182_checked (by decide +kernel))))) (by decide +kernel)

private theorem slopingSecondBlock5Part6 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (253/256) (1/1) ⟨(-3/4),(55/64),(-263/32768),(313/32768),(-263/32768),(313/32768)⟩ :=
  .relabel (.join (.join (.cell slopingFluxCell183 (253/256) (507/512) (-5/8) (55/64) (by decide +kernel) slopingFluxCell183_checked (by decide +kernel)) (.join (.cell slopingFluxCell184 (507/512) (127/128) (-41/64) (27/32) (by decide +kernel) slopingFluxCell184_checked (by decide +kernel)) (.cell slopingFluxCell185 (127/128) (509/512) (-43/64) (53/64) (by decide +kernel) slopingFluxCell185_checked (by decide +kernel)))) (.join (.cell slopingFluxCell186 (509/512) (255/256) (-45/64) (13/16) (by decide +kernel) slopingFluxCell186_checked (by decide +kernel)) (.join (.cell slopingFluxCell187 (255/256) (511/512) (-23/32) (25/32) (by decide +kernel) slopingFluxCell187_checked (by decide +kernel)) (.cell slopingFluxCell188 (511/512) (1/1) (-3/4) (49/64) (by decide +kernel) slopingFluxCell188_checked (by decide +kernel))))) (by decide +kernel)

theorem slopingSecondSpan56 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (225/256) (1/1) ⟨(-3/4),(81/32),(-395/16384),(1507/8192),(-943/32768),(1507/8192)⟩ :=
  .relabel (.join (.join slopingSecondBlock5Part0 (.join slopingSecondBlock5Part1 slopingSecondBlock5Part2)) (.join (.join slopingSecondBlock5Part3 slopingSecondBlock5Part4) (.join slopingSecondBlock5Part5 slopingSecondBlock5Part6))) (by decide +kernel)

theorem slopingSecondSpan02 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (0/1) (51/128) ⟨(-49/64),(175/64),(121/2048),(5813/8192),(-97/1024),(5813/8192)⟩ :=
  .relabel (.join slopingSecondSpan01 slopingSecondSpan12) (by decide +kernel)

theorem slopingSecondSpan15 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (3/16) (225/256) ⟨(3/64),(249/64),(11433/16384),(32327/16384),(0/1),(32327/16384)⟩ :=
  .relabel (.join (.join slopingSecondSpan12 slopingSecondSpan23) (.join slopingSecondSpan34 slopingSecondSpan45)) (by decide +kernel)

theorem slopingSecondSpan46 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (183/256) (1/1) ⟨(-3/4),(205/64),(1831/16384),(2733/4096),(-943/32768),(2733/4096)⟩ :=
  .relabel (.join slopingSecondSpan45 slopingSecondSpan56) (by decide +kernel)

theorem slopingSecondSpan26 :
    CheckedSlopingScalar false slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output
      (51/128) (1/1) ⟨(-3/4),(249/64),(4259/8192),(28079/16384),(-943/32768),(28079/16384)⟩ :=
  .relabel (.join (.join slopingSecondSpan23 slopingSecondSpan34) (.join slopingSecondSpan45 slopingSecondSpan56)) (by decide +kernel)

end TwoAxisHelicoid.TraceData
#print axioms TwoAxisHelicoid.TraceData.slopingFirstSpan02
#print axioms TwoAxisHelicoid.TraceData.slopingSecondSpan26
