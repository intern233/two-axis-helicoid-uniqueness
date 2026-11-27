import TwoAxisHelicoid.JacobiProductQuasiPeriod
import TwoAxisHelicoid.AnalyticSimpleQuotient
import TwoAxisHelicoid.ThetaAllSimpleZeros

namespace TwoAxisHelicoid
open Complex Set
set_option maxHeartbeats 0
attribute [local irreducible] thetaJet thetaScaledJet rhombicProductTheta

theorem thetaScaledJet_zero_add_two (t : ℝ) (z : ℂ) :
    thetaScaledJet t 0 (z+2) = -thetaScaledJet t 0 z := by
  have he : (Real.pi/2 : ℂ)*(z+2) = (Real.pi/2 : ℂ)*z+Real.pi := by ring
  simp only [thetaScaledJet, pow_zero, one_mul, he, thetaJet_add_pi]

theorem thetaScaledJet_zero_quasiperiod {t : ℝ} (ht : 0 < t) (z : ℂ) :
    thetaScaledJet t 0 (z+(1+I*t)) =
      thetaQuasiFactor t (Real.pi*z/2)*thetaScaledJet t 0 z := by
  have he : (Real.pi/2 : ℂ)*(z+(1+I*t)) =
      (Real.pi/2 : ℂ)*z+thetaComplexHalfPeriod t := by
    unfold thetaComplexHalfPeriod
    ring
  simp only [thetaScaledJet, pow_zero, one_mul, he, thetaJet_zero_quasiperiod ht]
  congr 2
  ring

theorem thetaScaledJet_simple_at_every_zero {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : thetaScaledJet t 0 z = 0) : deriv (thetaScaledJet t 0) z ≠ 0 := by
  rw [(thetaScaledJet_hasDerivAt ht 0 z).deriv]
  simp only [thetaScaledJet, pow_zero, one_mul] at hz
  simp only [thetaScaledJet, zero_add, pow_one]
  exact mul_ne_zero (div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (by norm_num))
    (thetaJet_simple_at_every_zero_of_pos ht hz)

theorem product_zero_of_theta_zero {t : ℝ} (ht : 0 < t) (z : ℂ)
    (hz : thetaScaledJet t 0 z = 0) : rhombicProductTheta t z = 0 := by
  apply rhombicProductTheta_zero_at_lattice ht
  apply (thetaJet_zero_iff_rhombic_lattice_of_pos ht z).mp
  simpa only [thetaScaledJet, pow_zero, one_mul, div_mul_eq_mul_div] using hz

noncomputable def jacobiThetaQuotient (t : ℝ) : ℂ → ℂ :=
  analyticSimpleQuotient (rhombicProductTheta t) (thetaScaledJet t 0)

theorem jacobiThetaQuotient_differentiable {t : ℝ} (ht : 0 < t) :
    Differentiable ℂ (jacobiThetaQuotient t) :=
  analyticSimpleQuotient_differentiable (rhombicProductTheta_differentiable ht)
    (fun z => (thetaScaledJet_hasDerivAt ht 0 z).differentiableAt)
    (product_zero_of_theta_zero ht)
    (fun _ hz => thetaScaledJet_simple_at_every_zero ht hz)

theorem jacobiThetaQuotient_period_two {t : ℝ} (ht : 0 < t) :
    Function.Periodic (jacobiThetaQuotient t) 2 := by
  apply analyticSimpleQuotient_periodic 2 (c := fun _ => -1)
    (rhombicProductTheta_differentiable ht)
    (fun z => (thetaScaledJet_hasDerivAt ht 0 z).differentiableAt)
    (by fun_prop) (by intro z; norm_num) (product_zero_of_theta_zero ht)
  · intro z
    simpa only [rhombicProductTheta, neg_one_mul] using
      jacobiThetaProduct_add_two (jacobiNome t) z
  · intro z
    simpa only [neg_one_mul] using thetaScaledJet_zero_add_two t z

theorem jacobiThetaQuotient_period_half {t : ℝ} (ht : 0 < t) :
    Function.Periodic (jacobiThetaQuotient t) (1+I*t) := by
  apply analyticSimpleQuotient_periodic (1+I*t)
    (c := fun z => thetaQuasiFactor t (Real.pi*z/2))
    (rhombicProductTheta_differentiable ht)
    (fun z => (thetaScaledJet_hasDerivAt ht 0 z).differentiableAt)
    (by unfold thetaQuasiFactor; fun_prop)
    (fun z => Complex.exp_ne_zero _) (product_zero_of_theta_zero ht)
  · exact rhombicProductTheta_quasiperiod ht
  · exact thetaScaledJet_zero_quasiperiod ht

theorem jacobiThetaQuotient_add_lattice {t : ℝ} (ht : 0 < t) (z : ℂ)
    {w : ℂ} (hw : w ∈ (rhombicPeriodPair t ht).lattice) :
    jacobiThetaQuotient t (z+w) = jacobiThetaQuotient t z := by
  obtain ⟨m,n,he⟩ := PeriodPair.mem_lattice.mp hw
  change (m : ℂ)*2+(n : ℂ)*(1+I*t) = w at he
  have h1 := (jacobiThetaQuotient_period_two ht).zsmul m z
  have h2 := (jacobiThetaQuotient_period_half ht).zsmul n (z+(m : ℂ)*2)
  simp only [zsmul_eq_mul] at h1 h2
  rw [← he, ← add_assoc, h2, h1]

theorem jacobiThetaQuotient_constant {t : ℝ} (ht : 0 < t) (z : ℂ) :
    jacobiThetaQuotient t z = jacobiThetaQuotient t 0 := by
  have hd := jacobiThetaQuotient_differentiable ht
  have hb := (IsZLattice.isCompact_range_of_periodic (rhombicPeriodPair t ht).lattice
    (jacobiThetaQuotient t) hd.continuous
    (fun z w hw => jacobiThetaQuotient_add_lattice ht z hw)).isBounded
  exact hd.apply_eq_apply_of_bounded hb z 0

/-- The actual theta series equals the Jacobi product up to its nonzero
normalization. This normalization cancels in all logarithmic derivatives and
normalized kernels used in the period problem. -/
theorem rhombicProductTheta_eq_scaled_theta {t : ℝ} (ht : 0 < t) (z : ℂ) :
    rhombicProductTheta t z =
      (deriv (rhombicProductTheta t) 0 / thetaScaledJet t 1 0)*thetaScaledJet t 0 z := by
  have h := analyticSimpleQuotient_mul (product_zero_of_theta_zero ht) z
  change jacobiThetaQuotient t z*thetaScaledJet t 0 z = rhombicProductTheta t z at h
  rw [jacobiThetaQuotient_constant ht] at h
  simpa [jacobiThetaQuotient, analyticSimpleQuotient, thetaScaledJet_zero_at_zero,
    (thetaScaledJet_hasDerivAt ht 0 0).deriv] using h.symm

theorem jacobiTheta_normalization_ne_zero {t : ℝ} (ht : 0 < t) :
    deriv (rhombicProductTheta t) 0 / thetaScaledJet t 1 0 ≠ 0 := by
  apply div_ne_zero _ (thetaScaledJet_one_ne_zero_of_pos ht)
  simpa only [rhombicProductTheta] using
    jacobiThetaProduct_deriv_zero_ne_zero (jacobiNome_norm_lt_one ht)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rhombicProductTheta_eq_scaled_theta
#print axioms TwoAxisHelicoid.jacobiTheta_normalization_ne_zero
