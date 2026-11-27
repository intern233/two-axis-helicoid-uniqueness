import TwoAxisHelicoid.UnitSpinorFrames

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 1000000

abbrev NonzeroSpinor := {s : ℂ × ℂ // s ≠ 0}

/-- Positive normalization of the actual spinor; its sign is retained. -/
noncomputable def normalizeSpinor (s : NonzeroSpinor) : UnitSpinor :=
  ⟨(Real.sqrt (spinorWeight s.1) : ℂ)⁻¹ • s.1,by
    rw [spinorWeight_smul,Complex.normSq_inv,Complex.normSq_ofReal,
      Real.mul_self_sqrt (spinorWeight_nonneg s.1)]
    exact inv_mul_cancel₀ (spinorWeight_pos s.2).ne'⟩

theorem normalizeSpinor_continuous : Continuous normalizeSpinor := by
  apply Continuous.subtype_mk
  have hc : Continuous (fun s : NonzeroSpinor => (Real.sqrt (spinorWeight s.1) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp (spinorWeight_continuous.comp continuous_subtype_val))
  have hi := hc.inv₀ (fun s =>
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (spinorWeight_pos s.2)).ne')
  simpa only [Pi.smul_apply] using! hi.smul
    (continuous_subtype_val : Continuous (fun s : NonzeroSpinor => s.1))

theorem normalizeSpinor_quadratic (s : NonzeroSpinor) :
    spinorQuadratic (normalizeSpinor s).1 =
      (spinorWeight s.1 : ℂ)⁻¹ • spinorQuadratic s.1 := by
  change spinorQuadratic ((Real.sqrt (spinorWeight s.1) : ℂ)⁻¹ • s.1) = _
  rw [spinorQuadratic_smul,inv_pow,← Complex.ofReal_pow,
    Real.sq_sqrt (spinorWeight_nonneg s.1)]

theorem normalizeSpinor_neg (s : NonzeroSpinor) :
    normalizeSpinor ⟨-s.1,neg_ne_zero.mpr s.2⟩ = unitSpinorAntipode (normalizeSpinor s) := by
  apply Subtype.ext
  change (Real.sqrt (spinorWeight (-s.1)) : ℂ)⁻¹ • (-s.1) =
    -((Real.sqrt (spinorWeight s.1) : ℂ)⁻¹ • s.1)
  rw [spinorWeight_neg,smul_neg]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.normalizeSpinor_quadratic
