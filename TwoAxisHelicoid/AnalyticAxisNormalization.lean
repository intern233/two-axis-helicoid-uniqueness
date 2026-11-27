import TwoAxisHelicoid.NormalizedAxisEnd

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology
set_option maxHeartbeats 1000000

noncomputable def centeredAxisEnd (α b : ℝ) (X : ℂ → Fin 3 → ℝ) (ξ : ℂ) : Fin 3 → ℝ :=
  verticalRotation I (α • (X (ξ/(α : ℂ))-![0,0,b]))

/-- A genuine analytic helicoidal end with one common vertical axis at
both real infinities has a normalized analytic profile and arbitrarily
thin tubes. This statement permits every nonzero pitch. -/
theorem analytic_axis_end_normalized_thin
    {X : ℂ → Fin 3 → ℝ} {f : ℂ → ℂ} {α : ℝ} (hα : α ≠ 0)
    (b R : ℝ) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (hX : ∀ ξ : ℂ, R < ‖ξ‖ → HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (I*(α : ℂ)*ξ+infinityCorrection f ξ)) 1)) ξ)
    (hh : ∀ ξ : ℂ, R < ‖ξ‖ → X ξ 2 = ξ.re+b)
    (haxis : ∃ A : ℝ, ∀ x : ℝ, A < |x| → X (x : ℂ) 0 = 0 ∧ X (x : ℂ) 1 = 0) :
    ∃ (g : ℂ → ℂ) (S : ℝ), AnalyticAt ℂ g 0 ∧
      (∀ ξ : ℂ, S < ‖ξ‖ → HasFDerivAt (centeredAxisEnd α b X)
        (nullRealDerivative (weierstrassTriple (exp (I*ξ+infinityCorrection g ξ)) 1)) ξ) ∧
      ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ ξ : ℂ, T < ‖ξ‖ →
        coordinateToTube (centeredAxisEnd α b X ξ) ∈ helicoidTubeEquiv.target ∧
        |helicoidSignedDistance (coordinateToTube (centeredAxisEnd α b X ξ))| ≤ ε := by
  let Y : ℂ → Fin 3 → ℝ := fun ξ => X ξ-![0,0,b]
  have hY ξ (hξ : R < ‖ξ‖) := (hX ξ hξ).sub_const (![0,0,b] : Fin 3 → ℝ)
  have hYh ξ (hξ : R < ‖ξ‖) : Y ξ 2 = ξ.re := by
    change X ξ 2-b = ξ.re
    rw [hh ξ hξ]
    ring
  have hYa : ∃ A : ℝ, ∀ x : ℝ, A < |x| → Y (x : ℂ) 0 = 0 ∧ Y (x : ℂ) 1 = 0 := by
    obtain ⟨A,hA⟩ := haxis
    refine ⟨A,?_⟩
    intro x hx
    change X (x : ℂ) 0-0 = 0 ∧ X (x : ℂ) 1-0 = 0
    simpa only [sub_zero] using hA x hx
  have hFt := infinityCorrection_tendsto_zero hf hf0
  obtain ⟨S,hS,_hFt,_haxis⟩ := nonzero_pitch_axis_end_normalized hα R hY hYh hFt hYa
  have hthin := nonzero_pitch_axis_end_arbitrarily_thin hα R hY hYh hFt hYa
  let g : ℂ → ℂ := fun w => f ((α : ℂ)*w)+(Real.pi : ℂ)/2*I
  have hg : AnalyticAt ℂ g 0 := by
    have hh : AnalyticAt ℂ f ((α : ℂ)*(0 : ℂ)) := by simpa only [mul_zero] using hf
    exact (hh.comp (analyticAt_const.mul analyticAt_id)).add analyticAt_const
  refine ⟨g,S,hg,?_,?_⟩
  · intro ξ hξ
    have hd := (verticalRotation I).hasFDerivAt.comp ξ (hS ξ hξ).1
    have he : exp (I*ξ+infinityCorrection g ξ) =
        I*exp (I*ξ+infinityCorrection f (ξ/(α : ℂ))) := by
      have hi : (ξ/(α : ℂ))⁻¹ = (α : ℂ)*ξ⁻¹ := by rw [inv_div,div_eq_mul_inv]
      dsimp only [infinityCorrection,g]
      rw [hi,← add_assoc,Complex.exp_add,Complex.exp_pi_div_two_mul_I,mul_comm]
    rw [he,nullRealDerivative_unit_multiplier (by norm_num : ‖(I : ℂ)‖ = 1)]
    change HasFDerivAt (fun w : ℂ => verticalRotation I (α • (X (w/(α : ℂ))-![0,0,b]))) _ ξ
    exact hd
  · simpa only [normalizeHeightEnd,Y,centeredAxisEnd] using hthin

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.analytic_axis_end_normalized_thin
