import TwoAxisHelicoid.RootUnitStrip

namespace TwoAxisHelicoid
open ComplexBall Set Filter
open scoped Topology
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_derivative_integrals_strong {t a : ℝ}
    (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ))
    (hal : (rootALower : ℝ) ≤ a) (hau : a ≤ (rootAUpper : ℝ)) :
    (∫ x : ℝ in (-1)..0, thetaAa t a ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ))).re < -4 ∧
    (∫ x : ℝ in (-1)..0, thetaAtMidline t a ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ))).re < -8 := by
  have hb := root_derivative_half_contains (by decide : 0 < 40) rootDerivativeParameters
    rootDerivativeParameters_valid rootDerivativeCells (1/20) rootDerivativeCells_valid htl htu hal hau
  have ha := (re_bounds hb.1).2
  have ht := (re_bounds hb.2).2
  have ca : (combineHorizontalCells (fun i => (rootDerivativeCells i).outputA.toBall rootDyadicConfig.prec)).center.re+
      (combineHorizontalCells (fun i => (rootDerivativeCells i).outputA.toBall rootDyadicConfig.prec )).radius < -4 := by decide +kernel
  have ct : (combineHorizontalCells (fun i => (rootDerivativeCells i).outputT.toBall rootDyadicConfig.prec)).center.re+
      (combineHorizontalCells (fun i => (rootDerivativeCells i).outputT.toBall rootDyadicConfig.prec)).radius < -8 := by decide +kernel
  constructor
  · apply lt_of_le_of_lt ha
    exact_mod_cast ca
  · apply lt_of_le_of_lt ht
    exact_mod_cast ct


theorem rootPeriodAlong_deriv_lt_neg_eight {t : ℝ}
    (ht : t ∈ Ioo (rootTLower:ℝ) rootTUpper) : deriv rootPeriodAlong t < -8 := by
  rw [(rootPeriodAlong_hasDerivAt ht).deriv]
  have ha := (rootVerticalAReal_spec ⟨ht.1.le,ht.2.le⟩).1
  have hn := root_derivative_integrals_strong ht.1.le ht.2.le ha.1.le ha.2.le
  change rootPeriodDa t (rootVerticalAReal t) < -4 ∧ rootPeriodDt t (rootVerticalAReal t) < -8 at hn
  have hneg : rootPeriodDa t (rootVerticalAReal t) < 0 := lt_trans hn.1 (by norm_num)
  have hm := mul_neg_of_pos_of_neg (rootVerticalAReal_deriv_pos ht) hneg
  linarith

theorem ellipticPeriodAlong_deriv_lt_neg_eight {t : ℝ}
    (ht : t ∈ Ioo (rootTLower:ℝ) rootTUpper) : deriv ellipticPeriodAlong t < -8 := by
  have he : ellipticPeriodAlong =ᶠ[𝓝 t] rootPeriodAlong := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact root_elliptic_along_eq hs
  rw [he.deriv_eq]
  exact rootPeriodAlong_deriv_lt_neg_eight ht

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ellipticPeriodAlong_deriv_lt_neg_eight
