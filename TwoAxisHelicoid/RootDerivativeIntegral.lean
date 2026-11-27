import TwoAxisHelicoid.RootDerivativeComposite
import TwoAxisHelicoid.RootDerivativeCell000
import TwoAxisHelicoid.RootDerivativeCell001
import TwoAxisHelicoid.RootDerivativeCell002
import TwoAxisHelicoid.RootDerivativeCell003
import TwoAxisHelicoid.RootDerivativeCell004
import TwoAxisHelicoid.RootDerivativeCell005
import TwoAxisHelicoid.RootDerivativeCell006
import TwoAxisHelicoid.RootDerivativeCell007
import TwoAxisHelicoid.RootDerivativeCell008
import TwoAxisHelicoid.RootDerivativeCell009
import TwoAxisHelicoid.RootDerivativeCell010
import TwoAxisHelicoid.RootDerivativeCell011
import TwoAxisHelicoid.RootDerivativeCell012
import TwoAxisHelicoid.RootDerivativeCell013
import TwoAxisHelicoid.RootDerivativeCell014
import TwoAxisHelicoid.RootDerivativeCell015
import TwoAxisHelicoid.RootDerivativeCell016
import TwoAxisHelicoid.RootDerivativeCell017
import TwoAxisHelicoid.RootDerivativeCell018
import TwoAxisHelicoid.RootDerivativeCell019
import TwoAxisHelicoid.RootDerivativeCell020
import TwoAxisHelicoid.RootDerivativeCell021
import TwoAxisHelicoid.RootDerivativeCell022
import TwoAxisHelicoid.RootDerivativeCell023
import TwoAxisHelicoid.RootDerivativeCell024
import TwoAxisHelicoid.RootDerivativeCell025
import TwoAxisHelicoid.RootDerivativeCell026
import TwoAxisHelicoid.RootDerivativeCell027
import TwoAxisHelicoid.RootDerivativeCell028
import TwoAxisHelicoid.RootDerivativeCell029
import TwoAxisHelicoid.RootDerivativeCell030
import TwoAxisHelicoid.RootDerivativeCell031
import TwoAxisHelicoid.RootDerivativeCell032
import TwoAxisHelicoid.RootDerivativeCell033
import TwoAxisHelicoid.RootDerivativeCell034
import TwoAxisHelicoid.RootDerivativeCell035
import TwoAxisHelicoid.RootDerivativeCell036
import TwoAxisHelicoid.RootDerivativeCell037
import TwoAxisHelicoid.RootDerivativeCell038
import TwoAxisHelicoid.RootDerivativeCell039

namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def rootDerivativeCells : Fin 40 → RootDerivativeCell := ![rootDerivativeCell000, rootDerivativeCell001, rootDerivativeCell002, rootDerivativeCell003, rootDerivativeCell004, rootDerivativeCell005, rootDerivativeCell006, rootDerivativeCell007, rootDerivativeCell008, rootDerivativeCell009, rootDerivativeCell010, rootDerivativeCell011, rootDerivativeCell012, rootDerivativeCell013, rootDerivativeCell014, rootDerivativeCell015, rootDerivativeCell016, rootDerivativeCell017, rootDerivativeCell018, rootDerivativeCell019, rootDerivativeCell020, rootDerivativeCell021, rootDerivativeCell022, rootDerivativeCell023, rootDerivativeCell024, rootDerivativeCell025, rootDerivativeCell026, rootDerivativeCell027, rootDerivativeCell028, rootDerivativeCell029, rootDerivativeCell030, rootDerivativeCell031, rootDerivativeCell032, rootDerivativeCell033, rootDerivativeCell034, rootDerivativeCell035, rootDerivativeCell036, rootDerivativeCell037, rootDerivativeCell038, rootDerivativeCell039]
theorem rootDerivativeCells_valid : ∀ i : Fin 40, (rootDerivativeCells i).Valid rootDerivativeParameters (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact rootDerivativeCell000_valid
  · exact rootDerivativeCell001_valid
  · exact rootDerivativeCell002_valid
  · exact rootDerivativeCell003_valid
  · exact rootDerivativeCell004_valid
  · exact rootDerivativeCell005_valid
  · exact rootDerivativeCell006_valid
  · exact rootDerivativeCell007_valid
  · exact rootDerivativeCell008_valid
  · exact rootDerivativeCell009_valid
  · exact rootDerivativeCell010_valid
  · exact rootDerivativeCell011_valid
  · exact rootDerivativeCell012_valid
  · exact rootDerivativeCell013_valid
  · exact rootDerivativeCell014_valid
  · exact rootDerivativeCell015_valid
  · exact rootDerivativeCell016_valid
  · exact rootDerivativeCell017_valid
  · exact rootDerivativeCell018_valid
  · exact rootDerivativeCell019_valid
  · exact rootDerivativeCell020_valid
  · exact rootDerivativeCell021_valid
  · exact rootDerivativeCell022_valid
  · exact rootDerivativeCell023_valid
  · exact rootDerivativeCell024_valid
  · exact rootDerivativeCell025_valid
  · exact rootDerivativeCell026_valid
  · exact rootDerivativeCell027_valid
  · exact rootDerivativeCell028_valid
  · exact rootDerivativeCell029_valid
  · exact rootDerivativeCell030_valid
  · exact rootDerivativeCell031_valid
  · exact rootDerivativeCell032_valid
  · exact rootDerivativeCell033_valid
  · exact rootDerivativeCell034_valid
  · exact rootDerivativeCell035_valid
  · exact rootDerivativeCell036_valid
  · exact rootDerivativeCell037_valid
  · exact rootDerivativeCell038_valid
  · exact rootDerivativeCell039_valid
theorem root_derivative_integrals_negative {t a : ℝ}
    (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ))
    (hal : (rootALower : ℝ) ≤ a) (hau : a ≤ (rootAUpper : ℝ)) :
    (∫ x : ℝ in (-1)..0, thetaAa t a ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ))).re < 0 ∧
    (∫ x : ℝ in (-1)..0, thetaAtMidline t a ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ))).re < 0 := by
  have hb := root_derivative_half_contains (by decide : 0 < 40) rootDerivativeParameters
    rootDerivativeParameters_valid rootDerivativeCells (1/20) rootDerivativeCells_valid htl htu hal hau
  have ha := (re_bounds hb.1).2
  have ht := (re_bounds hb.2).2
  have ca : (combineHorizontalCells (fun i => (rootDerivativeCells i).outputA.toBall rootDyadicConfig.prec)).center.re+
      (combineHorizontalCells (fun i => (rootDerivativeCells i).outputA.toBall rootDyadicConfig.prec)).radius < 0 := by decide +kernel
  have ct : (combineHorizontalCells (fun i => (rootDerivativeCells i).outputT.toBall rootDyadicConfig.prec)).center.re+
      (combineHorizontalCells (fun i => (rootDerivativeCells i).outputT.toBall rootDyadicConfig.prec)).radius < 0 := by decide +kernel
  constructor
  · apply lt_of_le_of_lt ha
    exact_mod_cast ca
  · apply lt_of_le_of_lt ht
    exact_mod_cast ct
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.root_derivative_integrals_negative
