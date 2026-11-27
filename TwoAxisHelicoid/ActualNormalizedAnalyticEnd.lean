import TwoAxisHelicoid.ActualPrimitiveThinEnd
import TwoAxisHelicoid.HeightInverseRegularity

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology
set_option maxHeartbeats 1000000

/-- One and the same actual height inverse supplies the analytic
Weierstrass profile, its regularity, both inverse identities, and arbitrary
thinness. The constant quarter-turn is included in the analytic correction. -/
theorem actual_periodic_primitive_normalized_analytic_thin_end
    {X : ℂ → Fin 3 → ℝ} {t a c : ℝ}
    (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (hp : ∀ z ω : ℂ, ω ∈ (rhombicPeriodPair t ht).lattice → X (z+ω) = X z) :
    ∃ (K f : ℂ → ℂ) (R : ℝ),
      Tendsto K (cobounded ℂ) (𝓝[≠] 0) ∧ AnalyticAt ℂ f 0 ∧
      (∀ᶠ ξ : ℂ in cobounded ℂ, AnalyticAt ℂ K ξ) ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), K (((2*(a-1)/c : ℝ) : ℂ)*actualComplexHeight t a c ht z) = z) ∧
      (∀ᶠ ξ : ℂ in cobounded ℂ, ((2*(a-1)/c : ℝ) : ℂ)*actualComplexHeight t a c ht (K ξ) = ξ) ∧
      (∀ ξ : ℂ, R < ‖ξ‖ → HasFDerivAt
        (fun ξ => axisNormalizedPrimitive (2*(a-1)/c) X (K ξ))
        (nullRealDerivative (weierstrassTriple (exp (I*ξ+infinityCorrection f ξ)) 1)) ξ) ∧
      ∀ ε : ℝ, 0 < ε → ∃ S : ℝ, ∀ ξ : ℂ, S < ‖ξ‖ →
        coordinateToTube (axisNormalizedPrimitive (2*(a-1)/c) X (K ξ)) ∈ helicoidTubeEquiv.target ∧
        |helicoidSignedDistance (coordinateToTube (axisNormalizedPrimitive (2*(a-1)/c) X (K ξ)))| ≤ ε := by
  let α : ℝ := 2*(a-1)/c
  have hα : α ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (ne_of_lt ha.2))) hc
  have hαc : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα
  obtain ⟨K,f,R₀,hK,hf,hf0,hKL,hcoord,haxis⟩ :=
    actual_periodic_primitive_centered_axis_end ht ha hc hX hp
  let Y : ℂ → Fin 3 → ℝ := fun ξ => verticalRotation I (X (K ξ))-verticalRotation I (X 1)
  let F := infinityCorrection f
  have hd ξ (hξ : R₀ < ‖ξ‖) := (hcoord ξ hξ).2.1
  have hheight ξ (hξ : R₀ < ‖ξ‖) := (hcoord ξ hξ).2.2
  have hFt := infinityCorrection_tendsto_zero hf hf0
  obtain ⟨R,hscaled,_hFt',_haxis'⟩ := nonzero_pitch_axis_end_normalized hα R₀ hd hheight hFt haxis
  have hthin := nonzero_pitch_axis_end_arbitrarily_thin hα R₀ hd hheight hFt haxis
  have hKR : ∀ᶠ ξ : ℂ in cobounded ℂ, actualComplexHeight t a c ht (K ξ) = ξ := by
    filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R₀)] with ξ hξ
    exact (hcoord ξ hξ).1
  have hKa := actual_height_inverse_eventually_analytic ht hc hK hKR
  have hdiv := complex_div_real_tendsto_cobounded hα
  let g : ℂ → ℂ := fun w => f ((α : ℂ)*w)+(Real.pi : ℂ)/2*I
  have hg : AnalyticAt ℂ g 0 := by
    have hh : AnalyticAt ℂ f ((α : ℂ)*(0 : ℂ)) := by simpa only [mul_zero] using hf
    exact (hh.comp (analyticAt_const.mul analyticAt_id)).add analyticAt_const
  refine ⟨(fun ξ => K (ξ/(α : ℂ))),g,R,hK.comp hdiv,hg,?_,?_,?_,?_,?_⟩
  · filter_upwards [hdiv.eventually hKa] with ξ hξ
    have hd : AnalyticAt ℂ (fun z : ℂ => z/(α : ℂ)) ξ :=
      analyticAt_id.div analyticAt_const hαc
    exact hξ.comp (f := fun z : ℂ => z/(α : ℂ)) hd
  · filter_upwards [hKL] with z hz
    change K (((α : ℂ)*actualComplexHeight t a c ht z)/(α : ℂ)) = z
    have he : ((α : ℂ)*actualComplexHeight t a c ht z)/(α : ℂ) = actualComplexHeight t a c ht z := by
      field_simp
    rwa [he]
  · filter_upwards [hdiv.eventually hKR] with ξ hξ
    change (α : ℂ)*actualComplexHeight t a c ht (K (ξ/(α : ℂ))) = ξ
    rw [hξ]
    field_simp
  · intro ξ hξ
    have hh := (verticalRotation I).hasFDerivAt.comp ξ (hscaled ξ hξ).1
    have he : exp (I*ξ+infinityCorrection g ξ) = I*exp (I*ξ+F (ξ/(α : ℂ))) := by
      have hi : (ξ/(α : ℂ))⁻¹ = (α : ℂ)*ξ⁻¹ := by rw [inv_div,div_eq_mul_inv]
      dsimp only [infinityCorrection,g,F]
      rw [hi,← add_assoc,Complex.exp_add,Complex.exp_pi_div_two_mul_I,mul_comm]
    rw [he,nullRealDerivative_unit_multiplier (by norm_num : ‖(I : ℂ)‖ = 1)]
    exact hh
  · intro ε hε
    exact hthin ε hε

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_periodic_primitive_normalized_analytic_thin_end
