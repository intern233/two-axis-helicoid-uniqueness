import TwoAxisHelicoid.JacobiChordPeriod

namespace TwoAxisHelicoid
open Complex Set Metric MeasureTheory
set_option maxHeartbeats 1000000
attribute [local irreducible] jacobiPairProduct jacobiProductError

noncomputable def jacobiChordPoint (t : ℝ) (z : ℂ) : ℂ :=
  (leftChordH (leftNome t) : ℂ)+I*(leftChordK (leftNome t) : ℂ)*z

noncomputable def jacobiChordKernel (t a : ℝ) (z : ℂ) : ℂ :=
  (I*(leftChordK (leftNome t) : ℂ))*jacobiChordDifferential t a (jacobiChordPoint t z)

theorem horizontalPeriod_eq_jacobiChordKernel {t a : ℝ} (ht : 0 < t) (htu : t ≤ 17/20)
    (ha0 : 0 < a) (ha1 : a < 1) :
    thetaHorizontalPeriod t a = (∫ s : ℝ in (-1)..1, jacobiChordKernel t a (s : ℂ)).re := by
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (fun v : ℝ => I*jacobiChordDifferential t a
      ((leftChordH (leftNome t) : ℂ)+I*(v : ℂ)))
    (leftChordK (leftNome t)) (a := -1) (b := 1)
  simp only [mul_neg_one, mul_one, Complex.real_smul] at hs
  rw [horizontalPeriod_eq_jacobiChord ht htu ha0 ha1]
  apply congrArg Complex.re
  rw [← hs, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  unfold jacobiChordKernel jacobiChordPoint
  push_cast
  ring

theorem horizontalPeriod_eq_jacobiChordKernel_to_seven_fifths {t a : ℝ} (ht : 0 < t) (htu : t ≤ 7/5)
    (ha0 : 0 < a) (ha1 : a < 1) :
    thetaHorizontalPeriod t a = (∫ s : ℝ in (-1)..1, jacobiChordKernel t a (s : ℂ)).re := by
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (fun v : ℝ => I*jacobiChordDifferential t a
      ((leftChordH (leftNome t) : ℂ)+I*(v : ℂ)))
    (leftChordK (leftNome t)) (a := -1) (b := 1)
  simp only [mul_neg_one, mul_one, Complex.real_smul] at hs
  rw [horizontalPeriod_eq_jacobiChord_to_seven_fifths ht htu ha0 ha1]
  apply congrArg Complex.re
  rw [← hs, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  unfold jacobiChordKernel jacobiChordPoint
  push_cast
  ring

theorem jacobiChordKernel_differentiableAt {t a : ℝ} (ht : 0 < t) {z : ℂ}
    (hm : jacobiChordPoint t z-I ≠ 0) (hp : jacobiChordPoint t z+I ≠ 0)
    (hqp : ‖jacobiNome (1/t)‖*‖jacobiChordX (jacobiChordPoint t z)‖ < 1)
    (hqm : ‖jacobiNome (1/t)‖*‖(jacobiChordX (jacobiChordPoint t z))⁻¹‖ < 1) :
    DifferentiableAt ℂ (jacobiChordKernel t a) z := by
  have hX : DifferentiableAt ℂ jacobiChordX (jacobiChordPoint t z) :=
    (differentiableAt_id.add_const I).div (differentiableAt_id.sub_const I) hm
  have hX0 : jacobiChordX (jacobiChordPoint t z) ≠ 0 := div_ne_zero hp hm
  have hE := jacobiProductError_differentiableAt (dualProductKappa t a)
    (jacobiNome_norm_lt_one (one_div_pos.mpr ht))
    (show (dualProductR t a : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
    hX0 hqp hqm
  have hD : DifferentiableAt ℂ (jacobiChordDifferential t a) (jacobiChordPoint t z) :=
    (leftChordDifferential_differentiableAt t (dualProductKappa t a)
      (sub_ne_zero.mp hm)).mul (hE.comp _ hX)
  exact (hD.comp z (by unfold jacobiChordPoint; fun_prop)).const_mul _

theorem jacobiChordKernel_continuous_real {t : ℝ} (ht : 0 < t)
    (hq : leftNome t ≤ 1/3) (a : ℝ) :
    Continuous (fun s : ℝ => jacobiChordKernel t a (s : ℂ)) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  have hre : (jacobiChordPoint t (s : ℂ)).re = leftChordH (leftNome t) := by
    simp [jacobiChordPoint]
  have hh := leftChordH_pos (leftNome_pos t)
  have hu : 0 < (jacobiChordPoint t (s : ℂ)).re := by rwa [hre]
  have hden := jacobiChord_den_ne_zero hu
  have hb := jacobiChordX_norm_bounds hh
    (show leftChordH (leftNome t)/2 < (jacobiChordPoint t (s : ℂ)).re by rw [hre]; linarith)
  have hn := jacobiChord_nome_bound (leftNome_pos t) hq
  have hQ : ‖jacobiNome (1/t)‖ = (leftNome t)^2 := by
    rw [jacobiNome_inverse_eq_leftNome ht]
    simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_sq]
  have hqp : ‖jacobiNome (1/t)‖*‖jacobiChordX (jacobiChordPoint t (s : ℂ))‖ < 1 := by
    rw [hQ]
    exact (mul_le_mul_of_nonneg_left hb.1 (sq_nonneg _)).trans_lt hn
  have hqm : ‖jacobiNome (1/t)‖*‖(jacobiChordX (jacobiChordPoint t (s : ℂ)))⁻¹‖ < 1 := by
    rw [hQ]
    exact (mul_le_mul_of_nonneg_left hb.2 (sq_nonneg _)).trans_lt hn
  exact (jacobiChordKernel_differentiableAt ht hden.1 hden.2 hqp hqm).continuousAt.comp
    (f := fun x : ℝ => (x : ℂ)) Complex.continuous_ofReal.continuousAt

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.horizontalPeriod_eq_jacobiChordKernel
#print axioms TwoAxisHelicoid.jacobiChordKernel_continuous_real
