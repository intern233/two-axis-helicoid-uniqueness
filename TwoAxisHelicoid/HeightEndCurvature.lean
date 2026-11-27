import TwoAxisHelicoid.WeierstrassSecondForm
import TwoAxisHelicoid.ExteriorPotentialIndex

namespace TwoAxisHelicoid
open Complex Matrix Filter Bornology
open scoped Topology

/-- Determinant of the actual second form divided by the determinant of
the actual conformal metric in the height coordinate. -/
noncomputable def logGaussGaussianCurvature (W : ℂ → ℂ) (z : ℂ) : ℝ :=
  Matrix.det (logGaussSecondForm W z)/(Real.cosh (W z).re)^4

theorem logGaussGaussianCurvature_formula {W : ℂ → ℂ} {D z : ℂ}
    (hW : HasDerivAt W D z) :
    logGaussGaussianCurvature W z = -‖D‖^2/(Real.cosh (W z).re)^4 := by
  unfold logGaussGaussianCurvature
  rw [logGaussSecondForm_formula hW,Matrix.det_fin_two]
  change ((-D.re)*D.re-D.im*D.im)/(Real.cosh (W z).re)^4 = _
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply]
  ring

theorem logGaussGaussianCurvature_bound {W : ℂ → ℂ} {D z : ℂ}
    (hW : HasDerivAt W D z) : |logGaussGaussianCurvature W z| ≤ ‖D‖^2 := by
  rw [logGaussGaussianCurvature_formula hW,abs_div,abs_neg,
    abs_of_nonneg (sq_nonneg _),abs_of_nonneg (by positivity : 0 ≤ (Real.cosh (W z).re)^4)]
  exact div_le_self (sq_nonneg _) (one_le_pow₀ (Real.one_le_cosh _))

/-- The analytic helicoidal end has an explicit uniform Gaussian
curvature bound outside a compact set. -/
theorem analytic_height_end_curvature_bounded (α : ℝ) {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) :
    ∀ᶠ z in cobounded ℂ,
      |logGaussGaussianCurvature (fun z => I*(α : ℂ)*z+infinityCorrection f z) z| ≤ (|α|+1)^2 := by
  have hs : ∀ᶠ z in cobounded ℂ, ‖deriv (infinityCorrection f) z‖ < 1 := by
    simpa only [Metric.mem_ball,dist_zero_right] using
      (infinityCorrection_deriv_tendsto_zero hf).eventually
        (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1))
  filter_upwards [infinityCorrection_eventually_analytic hf,hs] with z hz hn
  have hd := ((hasDerivAt_id z).const_mul (I*(α : ℂ))).add hz.differentiableAt.hasDerivAt
  simp only [mul_one] at hd
  have hnorm : ‖I*(α : ℂ)+deriv (infinityCorrection f) z‖ ≤ |α|+1 := by
    have hh := norm_add_le (I*(α : ℂ)) (deriv (infinityCorrection f) z)
    simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs] at hh
    linarith
  exact (logGaussGaussianCurvature_bound hd).trans
    (pow_le_pow_left₀ (norm_nonneg _) hnorm 2)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.analytic_height_end_curvature_bounded
