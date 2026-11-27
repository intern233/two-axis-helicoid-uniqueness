import TwoAxisHelicoid.QuadratureEnclosure

namespace TwoAxisHelicoid
open Complex Metric Set MeasureTheory

def QuadratureRule.momentDefect {K : ℕ} (q : QuadratureRule K) (j : ℕ) : ℚ :=
  monomialAverage j - ∑ i, q.weight i * (q.node i)^j

def QuadratureRule.momentErrorFactor {K : ℕ} (q : QuadratureRule K) (degree : ℕ) (ratio : ℚ) : ℚ :=
  (∑ j∈Finset.range degree, ratio^j * |q.momentDefect j|) +
    (1+q.weightNorm)*ratio^degree/(1-ratio)

theorem QuadratureRule.taylor_difference {K : ℕ} (q : QuadratureRule K) (f : ℂ → ℂ)
    (c : ℂ) (h : ℝ) (N : ℕ) :
    normalizedIntegral (analyticTaylor f c N) c h - q.apply (analyticTaylor f c N) c h =
      ∑ j∈Finset.range N, (((j.factorial:ℂ)⁻¹ * iteratedDeriv j f c)*(h:ℂ)^j)*(q.momentDefect j:ℂ) := by
  rw [normalizedIntegral_taylor]
  unfold QuadratureRule.apply analyticTaylor analyticTaylorTerm
  simp only [add_sub_cancel_left, mul_pow]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have reorder :
      ∑ i, (q.weight i:ℂ)*((j.factorial:ℂ)⁻¹*iteratedDeriv j f c*((h:ℂ)^j*(q.node i:ℂ)^j)) =
      ((j.factorial:ℂ)⁻¹*iteratedDeriv j f c*(h:ℂ)^j)*∑ i, (q.weight i:ℂ)*(q.node i:ℂ)^j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [reorder,← mul_sub]
  congr 1
  unfold QuadratureRule.momentDefect
  push_cast
  rfl

/-- Analytic quadrature with the exact signed discrepancy of each finite rational
moment. The geometric tail starts at the chosen degree independently of exactness. -/
theorem QuadratureRule.analytic_moment_error {K : ℕ} (q : QuadratureRule K) (N : ℕ) (hnode : q.NodesInUnit)
    {f : ℂ → ℂ} {c : ℂ} {h R M : ℝ} (hh : 0≤h) (hhR : h<R) (hM0 : 0≤M)
    (hf : DiffContOnCl ℂ f (ball c R)) (hM : ∀ z∈sphere c R, ‖f z‖≤M) :
    ‖normalizedIntegral f c h-q.apply f c h‖≤
      M * ((∑ j∈Finset.range N, (h/R)^j * |(q.momentDefect j:ℝ)|) +
        (1+(q.weightNorm:ℝ))*(h/R)^N/(1-h/R)) := by
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
  have term (j : ℕ) : ‖(j.factorial:ℂ)⁻¹*iteratedDeriv j f c*(h:ℂ)^j‖≤M*(h/R)^j := by
    have fbound : ‖(c+(h:ℂ))-c‖≤h := by rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh]
    have upper := analyticTaylorTerm_norm_le hR hh hf hM fbound j
    simpa only [analyticTaylorTerm,add_sub_cancel_left] using upper
  have diff : ‖normalizedIntegral p c h-q.apply p c h‖≤
      ∑ j∈Finset.range N, (M*(h/R)^j)*|(q.momentDefect j:ℝ)| := by
    rw [show p=analyticTaylor f c N from rfl,q.taylor_difference]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul,← Complex.ofReal_ratCast, Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (term j) (abs_nonneg _)
  calc
    _ = ‖(normalizedIntegral f c h-normalizedIntegral p c h) +
        (normalizedIntegral p c h-q.apply p c h) + (q.apply p c h-q.apply f c h)‖ := by congr 1; ring
    _ ≤ (‖normalizedIntegral f c h-normalizedIntegral p c h‖+‖normalizedIntegral p c h-q.apply p c h‖)
          + ‖q.apply p c h-q.apply f c h‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (E + ∑ j∈Finset.range N, (M*(h/R)^j)*|(q.momentDefect j:ℝ)|) + (q.weightNorm:ℝ)*E :=
      add_le_add (add_le_add hI diff) hQ
    _ = _ := by
      simp_rw [mul_assoc M]
      rw [← Finset.mul_sum]
      dsimp only [E]
      ring

theorem QuadratureRule.rational_moment_error {K : ℕ} (q : QuadratureRule K) (N : ℕ) (nodes : q.NodesInUnit)
    {c : ℂ} {h R M : ℚ} (hh : 0≤h) (inside : h<R) {f : ℂ → ℂ}
    (analytic : DiffContOnCl ℂ f (ball c (R:ℝ)))
    (bound : ∀ z∈closedBall c (R:ℝ), ‖f z‖≤(M:ℝ)) :
    ‖normalizedIntegral f c (h:ℝ)-q.apply f c (h:ℝ)‖ ≤
      ((M*q.momentErrorFactor N (h/R):ℚ):ℝ) := by
  have nonneg := (Rat.cast_nonneg (K:=ℝ)).mpr hh
  have lt := (Rat.cast_lt (K:=ℝ)).mpr inside
  have M0 := (norm_nonneg _).trans (bound _ (mem_closedBall_self (nonneg.trans lt.le)))
  have estimate := q.analytic_moment_error N nodes nonneg lt M0 analytic (fun z hz => bound z (sphere_subset_closedBall hz))
  unfold QuadratureRule.momentErrorFactor
  push_cast
  exact estimate

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.QuadratureRule.rational_moment_error
