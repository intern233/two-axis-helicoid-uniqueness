import TwoAxisHelicoid.WeierstrassControlledTails
import TwoAxisHelicoid.CoordinatePrimitiveUniqueness

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology

theorem real_complex_div_hasFDerivAt (α : ℝ) (z : ℂ) :
    HasFDerivAt (fun w : ℂ => w/(α : ℂ))
      ((α⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℂ) z := by
  have hh := ((ContinuousLinearMap.id ℝ ℂ).hasFDerivAt (x := z)).const_smul (α⁻¹ : ℝ)
  change HasFDerivAt (fun w : ℂ => (α⁻¹ : ℝ) • w)
    ((α⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℂ) z at hh
  simpa only [Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm] using hh

theorem scaled_height_end_hasFDerivAt {X : ℂ → Fin 3 → ℝ} {W : ℂ → ℂ}
    {α : ℝ} (hα : α ≠ 0) {z : ℂ}
    (hX : HasFDerivAt X (nullRealDerivative (weierstrassTriple (exp (W (z/(α : ℂ)))) 1)) (z/(α : ℂ))) :
    HasFDerivAt (fun w : ℂ => α • X (w/(α : ℂ)))
      (nullRealDerivative (weierstrassTriple (exp (W (z/(α : ℂ)))) 1)) z := by
  have hh := (hX.comp z (real_complex_div_hasFDerivAt α z)).const_smul α
  convert hh using 1
  · rfl
  · ext v j
    simp only [smul_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply,map_smul,Pi.smul_apply,smul_eq_mul]
    rw [← mul_assoc,mul_inv_cancel₀ hα,one_mul]

theorem complex_div_real_tendsto_cobounded {α : ℝ} (hα : α ≠ 0) :
    Tendsto (fun z : ℂ => z/(α : ℂ)) (cobounded ℂ) (cobounded ℂ) := by
  apply tendsto_norm_atTop_iff_cobounded.mp
  have hh := (tendsto_norm_cobounded_atTop (E := ℂ)).atTop_mul_const
    (inv_pos.mpr (abs_pos.mpr hα))
  simpa only [div_eq_mul_inv,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs] using! hh

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.scaled_height_end_hasFDerivAt
