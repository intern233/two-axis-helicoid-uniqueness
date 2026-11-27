import TwoAxisHelicoid.AxisHelicoidThin
import TwoAxisHelicoid.HeightEndScaling

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology
set_option maxHeartbeats 1000000

noncomputable def normalizeHeightEnd (α : ℝ) (X : ℂ → Fin 3 → ℝ) (z : ℂ) : Fin 3 → ℝ :=
  α • X (z/(α : ℂ))

theorem scaled_height_parameter_far {α : ℝ} (hα : α ≠ 0) (R : ℝ) {z : ℂ}
    (hz : |α| *(max R 0+1) < ‖z‖) : R < ‖z/(α : ℂ)‖ := by
  have ha : 0 < |α| := abs_pos.mpr hα
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs]
  have hh : max R 0+1 < ‖z‖/|α| := (lt_div_iff₀ ha).mpr (by simpa only [mul_comm] using hz)
  linarith [le_max_left R 0]

theorem nonzero_pitch_axis_end_normalized
    {X : ℂ → Fin 3 → ℝ} {F : ℂ → ℂ} {α : ℝ} (hα : α ≠ 0) (R₀ : ℝ)
    (hX : ∀ z : ℂ, R₀ < ‖z‖ → HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (I*(α : ℂ)*z+F z)) 1)) z)
    (hheight : ∀ z : ℂ, R₀ < ‖z‖ → X z 2 = z.re)
    (hF : Tendsto F (cobounded ℂ) (𝓝 0))
    (haxis : ∃ A : ℝ, ∀ x : ℝ, A < |x| → X (x : ℂ) 0 = 0 ∧ X (x : ℂ) 1 = 0) :
    ∃ R : ℝ,
      (∀ z : ℂ, R < ‖z‖ → HasFDerivAt (normalizeHeightEnd α X)
        (nullRealDerivative (weierstrassTriple (exp (I*z+F (z/(α : ℂ)))) 1)) z ∧
        normalizeHeightEnd α X z 2 = z.re) ∧
      Tendsto (fun z : ℂ => F (z/(α : ℂ))) (cobounded ℂ) (𝓝 0) ∧
      ∃ A : ℝ, ∀ x : ℝ, A < |x| →
        normalizeHeightEnd α X (x : ℂ) 0 = 0 ∧ normalizeHeightEnd α X (x : ℂ) 1 = 0 := by
  refine ⟨|α| *(max R₀ 0+1),?_,hF.comp (complex_div_real_tendsto_cobounded hα),?_⟩
  · intro z hz
    have harg := scaled_height_parameter_far hα R₀ hz
    have hαc : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα
    have he : I*(α : ℂ)*(z/(α : ℂ)) = I*z := by field_simp
    constructor
    · have hd := scaled_height_end_hasFDerivAt (W := fun w => I*(α : ℂ)*w+F w) hα (hX _ harg)
      change HasFDerivAt (fun w : ℂ => α • X (w/(α : ℂ))) _ z
      simpa only [he] using hd
    · change α*X (z/(α : ℂ)) 2 = z.re
      rw [hheight _ harg]
      simp only [div_eq_mul_inv,← Complex.ofReal_inv,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        mul_zero,sub_zero]
      field_simp
  · obtain ⟨A,hA⟩ := haxis
    refine ⟨|α| *(max A 0+1),?_⟩
    intro x hx
    have hx' : |α| *(max A 0+1) < ‖(x : ℂ)‖ := by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using hx
    have hh : A < |x/α| := by
      simpa only [← Complex.ofReal_div,Complex.norm_real,Real.norm_eq_abs] using
        scaled_height_parameter_far hα A hx'
    have he := hA (x/α) hh
    simp only [normalizeHeightEnd,← Complex.ofReal_div,Pi.smul_apply,smul_eq_mul,he.1,he.2,mul_zero,and_self]

theorem nonzero_pitch_axis_end_arbitrarily_thin
    {X : ℂ → Fin 3 → ℝ} {F : ℂ → ℂ} {α : ℝ} (hα : α ≠ 0) (R₀ : ℝ)
    (hX : ∀ z : ℂ, R₀ < ‖z‖ → HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (I*(α : ℂ)*z+F z)) 1)) z)
    (hheight : ∀ z : ℂ, R₀ < ‖z‖ → X z 2 = z.re)
    (hF : Tendsto F (cobounded ℂ) (𝓝 0))
    (haxis : ∃ A : ℝ, ∀ x : ℝ, A < |x| → X (x : ℂ) 0 = 0 ∧ X (x : ℂ) 1 = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ S : ℝ, ∀ z : ℂ, S < ‖z‖ →
      coordinateToTube (verticalRotation I (normalizeHeightEnd α X z)) ∈ helicoidTubeEquiv.target ∧
      |helicoidSignedDistance (coordinateToTube (verticalRotation I (normalizeHeightEnd α X z)))| ≤ ε := by
  obtain ⟨R,hR,hF',haxis'⟩ := nonzero_pitch_axis_end_normalized hα R₀ hX hheight hF haxis
  exact height_normalized_axis_end_arbitrarily_thin R (fun z hz => (hR z hz).1)
    (fun z hz => (hR z hz).2) hF' haxis'

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.nonzero_pitch_axis_end_arbitrarily_thin
