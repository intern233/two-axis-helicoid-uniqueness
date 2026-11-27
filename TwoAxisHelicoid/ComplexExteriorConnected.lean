import TwoAxisHelicoid.HeightEndProper
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace TwoAxisHelicoid
open Complex Set Metric

theorem complex_norm_exterior_isPreconnected {R : ℝ} (hR : 0 ≤ R) :
    IsPreconnected {z : ℂ | R < ‖z‖} := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [← Module.finrank_eq_rank,Complex.finrank_real_complex]
    norm_num
  have hs := (isPreconnected_sphere hrank (0 : ℂ) 1).prod
    (isPreconnected_Ioi : IsPreconnected (Ioi R))
  have he : (fun p : ℂ × ℝ => p.2 • p.1) '' (sphere (0 : ℂ) 1 ×ˢ Ioi R) =
      {z : ℂ | R < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨⟨u,r⟩,⟨hu,hr⟩,rfl⟩
      have hu' : ‖u‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hu
      change R < ‖r • u‖
      simpa [norm_smul,hu',Real.norm_eq_abs,abs_of_pos (hR.trans_lt hr)] using hr
    · intro hz
      have hn : ‖z‖ ≠ 0 := (hR.trans_lt hz).ne'
      refine ⟨((‖z‖⁻¹ : ℝ) • z,‖z‖),⟨?_,hz⟩,?_⟩
      · change dist ((‖z‖⁻¹ : ℝ) • z) 0 = 1
        rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)),
          inv_mul_cancel₀ hn]
      · change (‖z‖ : ℝ) • ((‖z‖⁻¹ : ℝ) • z) = z
        rw [smul_smul,mul_inv_cancel₀ hn,one_smul]
  rw [← he]
  exact hs.image _ (by fun_prop)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.complex_norm_exterior_isPreconnected
