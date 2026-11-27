import TwoAxisHelicoid.CoordinateAreaHessian

set_option autoImplicit false
namespace TwoAxisHelicoid
open Complex Set Filter Function Bornology
open scoped Topology ContDiff

/-- Compact test spaces with negative integral of the actual pointwise
normal area Hessian, in the given end coordinate. This makes no claim
about interchanging total-area differentiation and integration. -/
def HasInfiniteCompactCoordinateAreaIndexAtInfinity
    (X : ℂ → Fin 3 → ℝ) (W : ℂ → ℂ) : Prop :=
  ∀ R : ℝ, ∀ n : ℕ, ∃ v : Fin n → ℝ × ℝ → ℝ,
    (∀ i, ContDiff ℝ ∞ (v i) ∧ HasCompactSupport (v i)) ∧
    (∀ i, ∀ p ∈ tsupport (v i), R < ‖p‖) ∧ LinearIndependent ℝ v ∧
    ∀ c : Fin n → ℝ, c ≠ 0 →
      integratedCoordinateAreaHessian X W (fun p => ∑ i, c i*v i p) < 0

theorem finite_test_sum_support_exterior {n : ℕ} {v : Fin n → ℝ × ℝ → ℝ} {R : ℝ}
    (hfar : ∀ i, ∀ p ∈ tsupport (v i), R < ‖p‖) (c : Fin n → ℝ) :
    ∀ p ∈ tsupport (fun q => ∑ i, c i*v i q), R ≤ ‖p‖ := by
  intro p hp
  by_contra hn
  have hlt : ‖p‖ < R := lt_of_not_ge hn
  have hz : (fun q => ∑ i, c i*v i q) =ᶠ[𝓝 p] 0 := by
    filter_upwards [continuous_norm.continuousAt.eventually (Iio_mem_nhds hlt)] with q hq
    apply Finset.sum_eq_zero
    intro i _
    have hvi : v i q = 0 := by
      by_contra hnon
      exact (hfar i q (subset_closure hnon)).not_ge hq.le
    simp only [hvi,mul_zero]
  exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hp

/-- For any actual immersion with the stated Weierstrass differential on
an exterior region, the analytic helicoid end has arbitrary-dimensional
negative compact normal-variation spaces beyond every compact set. The
hypothesis specifies an actual derivative, not a postulated Jacobi form. -/
theorem analytic_helicoid_actual_coordinate_area_infinite_index
    {α : ℝ} (hα : α ≠ 0) {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0)
    {X : ℂ → Fin 3 → ℝ} {B : ℝ}
    (hX : ∀ p : ℝ × ℝ, B ≤ ‖p‖ → HasFDerivAt X
      (nullRealDerivative (weierstrassTriple
        (exp (I*(α : ℂ)*planeComplex p+infinityCorrection f (planeComplex p))) 1))
      (planeComplex p)) :
    HasInfiniteCompactCoordinateAreaIndexAtInfinity X
      (fun z => I*(α : ℂ)*z+infinityCorrection f z) := by
  obtain ⟨A,_,hA⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp
    (infinityCorrection_eventually_analytic hf)
  have hi := analytic_helicoid_gauss_normal_infinite_index hα hf h0
  intro R n
  let T := max R (max B A)
  obtain ⟨v,hv,hfar,hlin,hneg⟩ := hi T n
  refine ⟨v,hv,fun i p hp => (le_max_left _ _).trans_lt (hfar i p hp),hlin,?_⟩
  intro c hc
  have hsupport := finite_test_sum_support_exterior hfar c
  have hdiff : Differentiable ℝ (fun p => ∑ i, c i*v i p) := by
    have hvd (i : Fin n) : Differentiable ℝ (v i) := (hv i).1.differentiable (by simp)
    fun_prop
  rw [integratedCoordinateAreaHessian_eq_planar hdiff]
  · exact hneg c hc
  · intro p hp
    apply hX p
    exact (le_max_left B A).trans ((le_max_right R (max B A)).trans (hsupport p hp))
  · intro p hp
    have hAp : A ≤ ‖planeComplex p‖ :=
      (le_max_right B A).trans ((le_max_right R (max B A)).trans
        ((hsupport p hp).trans (norm_le_planeComplex_norm p)))
    exact (((hasDerivAt_id (planeComplex p)).const_mul (I*(α : ℂ))).add
      (hA hAp).differentiableAt.hasDerivAt).differentiableAt

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.analytic_helicoid_actual_coordinate_area_infinite_index
