import TwoAxisHelicoid.HeightEndAxisCenter
import TwoAxisHelicoid.NormalizedAxisEnd

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology
set_option maxHeartbeats 1000000

/-- A fixed spatial centering, signed dilation and two quarter turns. The
nonzero signed dilation has positive metric scale equal to its absolute
value. It does not depend on the end parameter. -/
noncomputable def axisNormalizedPrimitive (α : ℝ) (X : ℂ → Fin 3 → ℝ) (z : ℂ) : Fin 3 → ℝ :=
  verticalRotation I (α • (verticalRotation I (X z)-verticalRotation I (X 1)))

/-- The actual closed TwoAxisHelicoid coordinate forms have an arbitrarily thin
helicoidal end after an explicit fixed spatial similarity. The end chart
and both inverse identities are genuine. No thinness or HPR conclusion
is assumed: the common vertical axis and the analytic correction imply it. -/
theorem actual_periodic_primitive_arbitrarily_thin_end
    {X : ℂ → Fin 3 → ℝ} {t a c : ℝ}
    (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (hp : ∀ z ω : ℂ, ω ∈ (rhombicPeriodPair t ht).lattice → X (z+ω) = X z) :
    ∃ K : ℂ → ℂ,
      Tendsto K (cobounded ℂ) (𝓝[≠] 0) ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), K (((2*(a-1)/c : ℝ) : ℂ)*actualComplexHeight t a c ht z) = z) ∧
      (∀ᶠ ξ : ℂ in cobounded ℂ, ((2*(a-1)/c : ℝ) : ℂ)*actualComplexHeight t a c ht (K ξ) = ξ) ∧
      ∀ ε : ℝ, 0 < ε → ∃ S : ℝ, ∀ ξ : ℂ, S < ‖ξ‖ →
        coordinateToTube (axisNormalizedPrimitive (2*(a-1)/c) X (K ξ)) ∈ helicoidTubeEquiv.target ∧
        |helicoidSignedDistance (coordinateToTube (axisNormalizedPrimitive (2*(a-1)/c) X (K ξ)))| ≤ ε := by
  let α : ℝ := 2*(a-1)/c
  have hα : α ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (ne_of_lt ha.2))) hc
  have hαc : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα
  obtain ⟨K,f,R,hK,hf,hf0,hKL,hcoord,haxis⟩ :=
    actual_periodic_primitive_centered_axis_end ht ha hc hX hp
  let Y : ℂ → Fin 3 → ℝ := fun ξ => verticalRotation I (X (K ξ))-verticalRotation I (X 1)
  have hthin := nonzero_pitch_axis_end_arbitrarily_thin (X := Y) hα R
    (fun ξ hξ => (hcoord ξ hξ).2.1) (fun ξ hξ => (hcoord ξ hξ).2.2)
    (infinityCorrection_tendsto_zero hf hf0) haxis
  have hdiv := complex_div_real_tendsto_cobounded hα
  refine ⟨(fun ξ => K (ξ/(α : ℂ))),hK.comp hdiv,?_,?_,?_⟩
  · filter_upwards [hKL] with z hz
    change K (((α : ℂ)*actualComplexHeight t a c ht z)/(α : ℂ)) = z
    have he : ((α : ℂ)*actualComplexHeight t a c ht z)/(α : ℂ) = actualComplexHeight t a c ht z := by
      field_simp
    rw [he]
    exact hz
  · have hlarge : ∀ᶠ ξ : ℂ in cobounded ℂ, R < ‖ξ‖ :=
      tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)
    filter_upwards [hdiv.eventually hlarge] with ξ hξ
    change (α : ℂ)*actualComplexHeight t a c ht (K (ξ/(α : ℂ))) = ξ
    rw [(hcoord _ hξ).1]
    field_simp
  · intro ε hε
    obtain ⟨S,hS⟩ := hthin ε hε
    exact ⟨S,fun ξ hξ => hS ξ hξ⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_periodic_primitive_arbitrarily_thin_end
