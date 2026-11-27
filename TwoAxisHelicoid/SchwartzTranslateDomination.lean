import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.L2Space

namespace TwoAxisHelicoid
open MeasureTheory Real
open scoped SchwartzMap

/-- A single L² majorant dominates every translate of a planar Schwartz
test by an offset of norm at most R. -/
theorem plane_schwartz_shift_domination (φ : 𝓢(ℂ, ℂ)) {R : ℝ} (hR : 0≤R) :
    ∃ w : ℂ → ℝ, MemLp w 2 volume ∧
      ∀ z t : ℂ, ‖t‖≤R → ‖φ (z+t)‖≤w z := by
  let weight := fun z : ℂ => ((1+‖z‖)^2)⁻¹
  have pos (z : ℂ) : 0 < 1+‖z‖ := by positivity
  have wm : MemLp weight 2 volume := by
    apply (memLp_two_iff_integrable_sq (by dsimp only [weight]; fun_prop)).mpr
    have h := integrable_one_add_norm (μ:=volume) (E:=ℂ) (r:=4) (by rw [Complex.finrank_real_complex]; norm_num)
    convert h using 1
    funext z
    dsimp only [weight]
    rw [Real.rpow_neg (pos z).le]
    norm_num
    ring
  obtain ⟨M,bound⟩ : ∃ M : ℝ, ∀ z : ℂ, (1+‖z‖)^2 * ‖φ z‖≤M := by
    refine ⟨2^(2:ℕ) * ((Finset.Iic (2,0)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)) φ,fun z => ?_⟩
    simpa only [norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜:=ℝ) (m:=(2,0)) (k:=2) (n:=0) le_rfl le_rfl φ z
  refine ⟨fun z => ((1+R)^2*M)*weight z, wm.const_mul _,?_⟩
  intro z t ht
  have tri : ‖z‖≤‖z+t‖+‖t‖ := by simpa using norm_sub_le (z+t) t
  have sides : 1+‖z‖ ≤ (1+R)*(1+‖z+t‖) := by nlinarith [mul_nonneg hR (norm_nonneg (z+t))]
  have sq := pow_le_pow_left₀ (pos z).le sides 2
  have a := mul_le_mul_of_nonneg_right sq (norm_nonneg (φ (z+t)))
  have b := mul_le_mul_of_nonneg_left (bound (z+t)) (sq_nonneg (1+R))
  change ‖φ (z+t)‖≤((1+R)^2*M)*((1+‖z‖)^2)⁻¹
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos (pos z) 2), mul_comm]
  calc
    _ ≤ _ := a
    _ = (1+R)^2*((1+‖z+t‖)^2*‖φ (z+t)‖) := by ring
    _ ≤ _ := b

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.plane_schwartz_shift_domination

