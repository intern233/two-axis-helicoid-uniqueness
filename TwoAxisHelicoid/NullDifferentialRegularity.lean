import TwoAxisHelicoid.HolomorphicNullImmersion
import TwoAxisHelicoid.WeierstrassGeodesicFrame
import Mathlib.Analysis.Calculus.MeanValue

namespace TwoAxisHelicoid
open Complex Set Metric Filter
open scoped Topology ContDiff

/-- A real map with the real part of a holomorphic differential is itself
real analytic locally. No regularity of a chosen primitive is assumed. -/
theorem analyticAt_of_holomorphic_real_differential
    {X : ℂ → Fin 3 → ℝ} {Φ : ℂ → Fin 3 → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hΦ : AnalyticOnNhd ℂ Φ U)
    (hX : ∀ z ∈ U, HasFDerivAt X (nullRealDerivative (Φ z)) z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) : AnalyticAt ℝ X z₀ := by
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz₀)
  have hd : DifferentiableOn ℂ Φ (ball z₀ r) :=
    fun z hz => (hΦ z (hrU hz)).differentiableAt.differentiableWithinAt
  obtain ⟨F,_hF₀,hF⟩ := hd.isExactOn_ball.with_val_at z₀ 0
  have hFa : AnalyticOnNhd ℂ F (ball z₀ r) :=
    (show DifferentiableOn ℂ F (ball z₀ r) from
      fun z hz => (hF z hz).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball
  let Y : ℂ → Fin 3 → ℝ := fun w => coordinateRealPart (F w)
  have hY z (hz : z ∈ ball z₀ r) : HasFDerivAt Y (nullRealDerivative (Φ z)) z :=
    realPart_primitive_hasFDerivAt (hF z hz)
  obtain ⟨b,hb⟩ := isOpen_ball.exists_eq_add_of_fderiv_eq
    (convex_ball z₀ r).isPreconnected
    (fun z hz => (hX z (hrU hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => (hY z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [(hX z (hrU hz)).fderiv,(hY z hz).fderiv])
  have hYa : AnalyticAt ℝ Y z₀ :=
    (coordinateRealPart.analyticAt (F z₀)).comp
      ((hFa z₀ (mem_ball_self hr)).restrictScalars (𝕜 := ℝ))
  exact (hYa.add analyticAt_const).congr
    (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_self hr)) hb).symm

theorem analyticAt_weierstrass_exp_triple {W : ℂ → ℂ} {z : ℂ}
    (hW : AnalyticAt ℂ W z) :
    AnalyticAt ℂ (fun w => weierstrassTriple (exp (W w)) 1) z := by
  have he : (fun w => weierstrassTriple (exp (W w)) 1) =
      fun w => ![-sinh (W w),I*cosh (W w),1] := by
    funext w
    exact weierstrassTriple_exp (W w)
  rw [he]
  apply AnalyticAt.pi
  intro j
  fin_cases j
  · simpa only [Matrix.cons_val_zero,Function.comp_def,Pi.neg_apply] using!
      (Complex.analyticAt_sinh.comp hW).neg
  · simpa only [Matrix.cons_val_one,Matrix.cons_val_zero,Function.comp_def,Pi.mul_apply] using!
      analyticAt_const.mul (Complex.analyticAt_cosh.comp hW)
  · simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) z)

theorem weierstrass_exp_real_derivative_injective (z : ℂ) :
    Function.Injective (nullRealDerivative (weierstrassTriple (exp z) 1)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change nullRealDerivative (weierstrassTriple (exp z) 1) v = 0 at hv
  have he := weierstrass_exp_direction_metric z v
  rw [hv] at he
  simp only [Pi.zero_apply,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero] at he
  exact Complex.normSq_eq_zero.mp
    ((mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ (Real.cosh_pos _).ne'))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.analyticAt_of_holomorphic_real_differential
