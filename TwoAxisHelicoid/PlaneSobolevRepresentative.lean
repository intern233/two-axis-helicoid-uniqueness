import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace TwoAxisHelicoid
open MeasureTheory FourierTransform TemperedDistribution Real
open scoped SchwartzMap ContDiff BoundedContinuousFunction RealInnerProductSpace

/-- Inverse Fourier transformation pairs an integrable frequency field with
the same inverse transform on a Schwartz test. -/
theorem plane_inverse_fourier_test_pairing (g : ℂ → ℂ) (hg : Integrable g)
    (φ : 𝓢(ℂ, ℂ)) :
    (∫ z, (𝓕⁻ φ) z • g z) = ∫ z, φ z • 𝓕⁻ g z := by
  have continuousPair : Continuous (fun p : ℂ × ℂ => (-innerₗ ℂ) p.1 p.2) := continuous_inner.neg
  have flip : (-innerₗ ℂ).flip = -innerₗ ℂ := by
    ext x y
    change -inner ℝ y x = -inner ℝ x y
    rw [real_inner_comm y x]
  have e := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ:=volume) (ν:=volume) (L := -innerₗ ℂ)
    Real.continuous_fourierChar continuousPair φ.integrable hg
  rw [flip] at e
  have point (z : ℂ) : (𝓕⁻ φ) z = (𝓕⁻ (⇑φ : ℂ → ℂ)) z := congrFun (SchwartzMap.fourierInv_coe φ) z
  simp_rw [point]
  exact e

/-- Above order one in dimension two the actual square-integrable field
agrees almost everywhere with a bounded continuous, pointwise-defined map. -/
theorem plane_sobolev_continuous_representative (u : Lp ℂ 2 (volume : Measure ℂ))
    {s : ℝ} (hs : 1 < s) (reg : MemSobolev s 2 (u : 𝓢'(ℂ, ℂ))) :
    ∃ f : ℂ →ᵇ ℂ, ⇑u =ᵐ[volume] ⇑f := by
  obtain ⟨g,hg⟩ := reg.fourier_memL1 (by rw [Complex.finrank_real_complex]; push_cast; linarith)
  let f := Lp.fourierTransformInv g
  refine ⟨f,?_⟩
  apply ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp u).locallyIntegrable (by norm_num))
    f.continuous.locallyIntegrable
  intro ψ smooth support
  have hc : HasCompactSupport (Complex.ofRealCLM ∘ ψ) := support.comp_left rfl
  have sc : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ ψ) := Complex.ofRealCLM.contDiff.comp smooth
  let φ := hc.toSchwartzMap sc
  have id : (u : 𝓢'(ℂ, ℂ)) = 𝓕⁻ (g : 𝓢'(ℂ, ℂ)) := by
    rw [← hg, fourierInv_fourier_eq]
  have eq := congrArg (fun U : 𝓢'(ℂ, ℂ) => U φ) id
  change (Lp.toTemperedDistribution u) φ = (Lp.toTemperedDistribution g) (𝓕⁻ φ) at eq
  rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply,
    plane_inverse_fourier_test_pairing _ (L1.integrable_coeFn g)] at eq
  simpa [φ,f] using eq

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.plane_sobolev_continuous_representative

