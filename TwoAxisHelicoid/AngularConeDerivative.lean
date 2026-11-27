import TwoAxisHelicoid.VerticalAxisDividedDifference
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace TwoAxisHelicoid
open Complex Set Topology Filter NormedSpace
open scoped Topology

/-- At a zero of a differentiable complex map, a homogeneous angular
bound on its nearby values holds for all its actual derivative vectors. -/
theorem relative_horizontal_derivative_cone {P : ℂ → ℂ} {z : ℂ} {ε : ℝ} (dp : DifferentiableAt ℝ P z)
    (zero : P z=0) (cone : ∀ᶠ w in 𝓝 z, |(P w).im|≤ε*‖P w‖) (v : ℂ) :
    |(fderiv ℝ P z v).im|≤ε*‖fderiv ℝ P z v‖ := by
  let γ := fun s : ℝ => z+s • v
  have h0 : γ 0=z := by simp [γ]
  have dg : HasDerivAt γ v 0 := by
    simpa only [Pi.add_apply,zero_add,one_smul] using! (hasDerivAt_const (0:ℝ) z).add ((hasDerivAt_id 0).smul_const v)
  have hg := (show HasFDerivAt P (fderiv ℝ P z) (γ 0) from h0.symm ▸ dp.hasFDerivAt).comp_hasDerivAt 0 dg
  have lim : Tendsto (fun s : ℝ => s⁻¹ • P (γ s)) (𝓝[>] 0) (𝓝 (fderiv ℝ P z v)) := by
    simpa only [Function.comp_apply,zero_add,h0,zero,sub_zero] using hg.tendsto_slope_zero_right
  have near : Tendsto γ (𝓝[>] 0) (𝓝 z) := h0 ▸ dg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto (Complex.continuous_im.continuousAt.tendsto.comp lim |>.abs)
    (tendsto_const_nhds.mul lim.norm)
  filter_upwards [near.eventually cone] with s hs
  change |(s⁻¹ • P (γ s)).im|≤ε*‖s⁻¹ • P (γ s)‖
  rw [Complex.real_smul,Complex.im_ofReal_mul,abs_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  calc |s⁻¹| * |(P (γ s)).im| ≤ |s⁻¹| * (ε*‖P (γ s)‖) := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ = _ := by ring

theorem normalized_complex_im_le_of_cone {z : ℂ} {ε : ℝ} (hε : 0≤ε) (h : |z.im|≤ε*‖z‖) :
    |(NormedSpace.normalize z).im|≤ε := by
  by_cases hz : z=0
  · simpa [hz] using hε
  have n := norm_pos_iff.mpr hz
  simp only [NormedSpace.normalize,Complex.real_smul,Complex.im_ofReal_mul,abs_mul,abs_of_pos (inv_pos.mpr n)]
  calc ‖z‖⁻¹*|z.im| ≤ ‖z‖⁻¹*(ε*‖z‖) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr n.le)
    _ = ε := by field_simp

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.relative_horizontal_derivative_cone
#print axioms TwoAxisHelicoid.normalized_complex_im_le_of_cone
