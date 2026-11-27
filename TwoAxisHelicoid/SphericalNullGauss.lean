import TwoAxisHelicoid.GaussFromVerticalRotation
import TwoAxisHelicoid.WeierstrassSimilarity
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped OnePoint Topology ComplexConjugate

/-- The stereographic Gauss data including the point at infinity. -/
noncomputable def sphericalNullGauss (p : Fin 3 → ℂ) : OnePoint ℂ :=
  if nullHorizontalMinus p = 0 then ∞ else ↑(nullGauss p)

private noncomputable def inverseSphereChart (z : ℂ) : OnePoint ℂ := if z = 0 then ∞ else ↑(z⁻¹)

private theorem inverseSphereChart_continuous : Continuous inverseSphereChart := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z = 0
  · subst z
    rw [continuousAt_iff_punctured_nhds]
    have h : Tendsto (fun w : ℂ => (↑(w⁻¹) : OnePoint ℂ)) (𝓝[≠] 0) (𝓝 ∞) := by
      apply OnePoint.tendsto_coe_infty.comp
      rw [coclosedCompact_eq_cocompact,← Metric.cobounded_eq_cocompact]
      exact Filter.tendsto_inv₀_nhdsNE_zero
    rw [show inverseSphereChart 0 = ∞ by simp [inverseSphereChart]]
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with w hw
    simp [inverseSphereChart,show w ≠ 0 from hw]
  · apply (OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)).congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    simp [inverseSphereChart,hw]

private theorem sphericalNullGauss_eq_inverse {p : Fin 3 → ℂ} (hp : ComplexNull p) (hplus : nullHorizontalPlus p ≠ 0) :
    sphericalNullGauss p = inverseSphereChart (-p 2/nullHorizontalPlus p) := by
  rw [← null_gauss_inverse_eq hp hplus]
  by_cases hm : nullHorizontalMinus p = 0
  · simp [sphericalNullGauss,hm,inverseSphereChart,nullGauss]
  · have h2 : p 2 ≠ 0 := by
      intro h
      have he := null_horizontal_product hp
      rw [h] at he
      exact (mul_ne_zero hm hplus) (by simpa using he)
    have hg : nullGauss p ≠ 0 := div_ne_zero h2 hm
    simp [sphericalNullGauss,hm,inverseSphereChart,hg]

/-- At a polar point the reciprocal stereographic chart is regular,
so the sphere-valued Gauss map really is continuous across that point
and distinguishes it from a Gauss zero. -/
theorem sphericalNullGauss_continuousAt {u : ℂ → Fin 3 → ℂ} {z : ℂ}
    (hu : ∀ j, ContinuousAt (fun w => u w j) z) (hn : u z ≠ 0)
    (hp : ∀ᶠ w in 𝓝 z, ComplexNull (u w)) :
    ContinuousAt (fun w => sphericalNullGauss (u w)) z := by
  have hplus : ContinuousAt (fun w => nullHorizontalPlus (u w)) z := (hu 0).add (continuousAt_const.mul (hu 1))
  have hminus : ContinuousAt (fun w => nullHorizontalMinus (u w)) z := (hu 0).sub (continuousAt_const.mul (hu 1))
  by_cases h : nullHorizontalMinus (u z) = 0
  · have hh : nullHorizontalPlus (u z) ≠ 0 := (null_horizontal_not_both_zero hp.self_of_nhds hn).resolve_left (fun h' => h' h)
    apply (inverseSphereChart_continuous.continuousAt.comp ((hu 2).neg.div hplus hh)).congr_of_eventuallyEq
    filter_upwards [hp,hplus.eventually_ne hh] with w hw hw'
    exact sphericalNullGauss_eq_inverse hw hw'
  · apply (OnePoint.continuous_coe.continuousAt.comp ((hu 2).div hminus h)).congr_of_eventuallyEq
    filter_upwards [hminus.eventually_ne h] with w hw
    simp only [sphericalNullGauss,ite_eq_right hw,nullGauss,Function.comp_apply,Pi.div_apply]

/-- Rotation of the actual position derivative rotates the complex
stereographic coordinate and fixes the north pole exactly. -/
theorem sphericalNullGauss_of_rotated_real_derivative {p q : Fin 3 → ℂ} {c : ℂ} (hc : ‖c‖ = 1)
    (h : nullRealDerivative q = (verticalRotation c).comp (nullRealDerivative p)) :
    sphericalNullGauss q = OnePoint.map (c*·) (sphericalNullGauss p) := by
  have hv := h.trans (nullRealDerivative_complexVerticalRotation c p).symm
  have he : q = complexVerticalRotation c p := by
    funext j
    apply Complex.ext
    · simpa using congrArg (fun f : ℂ →L[ℝ] (Fin 3 → ℝ) => f 1 j) hv
    · simpa using congrArg (fun f : ℂ →L[ℝ] (Fin 3 → ℝ) => f I j) hv
  have hm : nullHorizontalMinus q = conj c*nullHorizontalMinus p := by
    rw [he]
    apply Complex.ext <;> simp [nullHorizontalMinus,complexVerticalRotation,Complex.mul_re,Complex.mul_im] <;> ring
  have hc' : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; norm_num)
  by_cases h₀ : nullHorizontalMinus p = 0
  · simp [sphericalNullGauss,h₀,hm]
  · simp [sphericalNullGauss,h₀,hm,hc',nullGauss_of_rotated_real_derivative hc h]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.sphericalNullGauss_continuousAt
#print axioms TwoAxisHelicoid.sphericalNullGauss_of_rotated_real_derivative
