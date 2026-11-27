import TwoAxisHelicoid.QuadratureRule

namespace TwoAxisHelicoid
open Set Metric MeasureTheory
open scoped Interval

theorem affine_unit_norm_bound {c : ℂ} {h x : ℝ} (hh : 0 ≤ h)
    (hx : x ∈ Icc (-1 : ℝ) 1) : ‖(c+(h : ℂ)*(x : ℂ))-c‖ ≤ h := by
  rw [add_sub_cancel_left, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hh]
  have hx' : |x| ≤ 1 := abs_le.mpr hx
  simpa using mul_le_mul_of_nonneg_left hx' hh

theorem analyticTaylor_continuous (f : ℂ → ℂ) (c : ℂ) (N : ℕ) :
    Continuous (analyticTaylor f c N) := by
  unfold analyticTaylor analyticTaylorTerm
  fun_prop

theorem QuadratureRule.apply_sub_bound {K : ℕ} (q : QuadratureRule K)
    {f p : ℂ → ℂ} {c : ℂ} {h E : ℝ}
    (hE : ∀ i, ‖p (c+(h : ℂ)*(q.node i : ℂ))-f (c+(h : ℂ)*(q.node i : ℂ))‖ ≤ E) :
    ‖q.apply p c h-q.apply f c h‖ ≤ (q.weightNorm : ℝ)*E := by
  unfold QuadratureRule.apply QuadratureRule.weightNorm
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖(q.weight i : ℂ)*p (c+(h : ℂ)*(q.node i : ℂ))-
        (q.weight i : ℂ)*f (c+(h : ℂ)*(q.node i : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ i, (|q.weight i| : ℚ)*E := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← mul_sub, norm_mul, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
      push_cast
      exact mul_le_mul_of_nonneg_left (hE i) (abs_nonneg _)
    _ = _ := by push_cast; rw [Finset.sum_mul]

/-- A rigorously bounded quadrature rule: exact rational moments cancel every
Taylor term below N, and Cauchy's estimate bounds the remaining infinite series. -/
theorem QuadratureRule.analytic_error_bound {K N : ℕ} {q : QuadratureRule K}
    (hq : q.ExactTo N) (hnode : q.NodesInUnit)
    {f : ℂ → ℂ} {c : ℂ} {h R M : ℝ}
    (hh : 0 ≤ h) (hhR : h < R) (hM0 : 0 ≤ M)
    (hf : DiffContOnCl ℂ f (ball c R))
    (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) :
    ‖normalizedIntegral f c h-q.apply f c h‖ ≤
      (1+(q.weightNorm : ℝ))*(M*(h/R)^N/(1-h/R)) := by
  have hR : 0 < R := hh.trans_lt hhR
  let p := analyticTaylor f c N
  let E := M*(h/R)^N/(1-h/R)
  have hb : ∀ x ∈ Icc (-1 : ℝ) 1,
      ‖f (c+(h : ℂ)*(x : ℂ))-p (c+(h : ℂ)*(x : ℂ))‖ ≤ E := by
    intro x hx
    exact analyticTaylor_remainder_bound hR hh hhR hM0 hf hM (affine_unit_norm_bound hh hx) N
  have hcf : ContinuousOn (fun x : ℝ => f (c+(h : ℂ)*(x : ℂ))) (Icc (-1 : ℝ) 1) :=
    hf.continuousOn_ball.comp (by fun_prop) (fun x hx =>
      mem_closedBall_iff_norm.mpr ((affine_unit_norm_bound hh hx).trans hhR.le))
  have hcp : Continuous (fun x : ℝ => p (c+(h : ℂ)*(x : ℂ))) :=
    (analyticTaylor_continuous f c N).comp (by fun_prop)
  have hif := hcf.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (-1 : ℝ) ≤ 1)
  have hip := hcp.intervalIntegrable (-1) 1 (μ := volume)
  have hI : ‖normalizedIntegral f c h-normalizedIntegral p c h‖ ≤ E := by
    unfold normalizedIntegral
    rw [← mul_sub, ← intervalIntegral.integral_sub hif hip, norm_mul]
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-1 : ℝ)) (b := 1) (fun x hx => hb x
        (by norm_num [uIoc] at hx; exact ⟨hx.1.le, hx.2⟩))
    norm_num at hnorm ⊢
    linarith
  have hQ : ‖q.apply p c h-q.apply f c h‖ ≤ (q.weightNorm : ℝ)*E := by
    apply q.apply_sub_bound
    intro i
    rw [norm_sub_rev]
    apply hb
    change (-1 : ℝ) ≤ (q.node i : ℝ) ∧ (q.node i : ℝ) ≤ 1
    exact_mod_cast hnode i
  have he : q.apply p c h = normalizedIntegral p c h := q.exact_taylor hq f c h
  calc
    _ = ‖(normalizedIntegral f c h-normalizedIntegral p c h)+
        (q.apply p c h-q.apply f c h)‖ := by rw [he]; congr 1; ring
    _ ≤ ‖normalizedIntegral f c h-normalizedIntegral p c h‖+
        ‖q.apply p c h-q.apply f c h‖ := norm_add_le _ _
    _ ≤ E+(q.weightNorm : ℝ)*E := add_le_add hI hQ
    _ = _ := by dsimp [E]; ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.QuadratureRule.analytic_error_bound
