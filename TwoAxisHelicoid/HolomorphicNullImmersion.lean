import TwoAxisHelicoid.NullVectorRegularity
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

namespace TwoAxisHelicoid
open Complex Set Metric InnerProductSpace
open scoped Topology

noncomputable def coordinateRealPart : (Fin 3 → ℂ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi (fun j => Complex.reCLM.comp (ContinuousLinearMap.proj j))

@[simp] theorem coordinateRealPart_apply (v : Fin 3 → ℂ) (j : Fin 3) :
    coordinateRealPart v j = (v j).re := rfl

noncomputable def nullRealDerivative (p : Fin 3 → ℂ) : ℂ →L[ℝ] (Fin 3 → ℝ) :=
  coordinateRealPart.comp
    ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) p).restrictScalars ℝ)

@[simp] theorem nullRealDerivative_apply (p : Fin 3 → ℂ) (w : ℂ) (j : Fin 3) :
    nullRealDerivative p w j = (w*p j).re := rfl

theorem nullRealDerivative_injective {p : Fin 3 → ℂ} (hp : ComplexNull p) (hn : p ≠ 0) :
    Function.Injective (nullRealDerivative p) := nullVector_real_map_injective hp hn

theorem nullRealDerivative_conformal {p : Fin 3 → ℂ} (hp : ComplexNull p) (hn : p ≠ 0) :
    0 < nullMetric p ∧
      (∑ j, (nullRealDerivative p 1 j)^2) = nullMetric p ∧
      (∑ j, (nullRealDerivative p I j)^2) = nullMetric p ∧
      (∑ j, nullRealDerivative p 1 j*nullRealDerivative p I j) = 0 := by
  have hid := complexNull_real_identities hp
  refine ⟨nullMetric_pos hp hn,?_,?_,?_⟩
  · simp [Fin.sum_univ_succ,nullMetric,add_assoc]
  · simpa [Fin.sum_univ_succ,Complex.mul_re,add_assoc] using hid.1.symm
  · simpa [Fin.sum_univ_succ,Complex.mul_re,add_assoc] using congrArg Neg.neg hid.2

theorem realPart_primitive_hasFDerivAt {F : ℂ → Fin 3 → ℂ} {p : Fin 3 → ℂ} {z : ℂ}
    (hF : HasDerivAt F p z) :
    HasFDerivAt (fun w => coordinateRealPart (F w)) (nullRealDerivative p) z := by
  exact coordinateRealPart.hasFDerivAt.comp z (hF.hasFDerivAt.restrictScalars ℝ)

/-- Local Weierstrass representation, with injectivity and conformality of the
real derivative and harmonicity proved explicitly. No global periods are assumed. -/
theorem holomorphic_null_local_immersion {Φ : ℂ → Fin 3 → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hΦ : AnalyticOnNhd ℂ Φ U)
    (hnull : ∀ z ∈ U, ComplexNull (Φ z)) (hn : ∀ z ∈ U, Φ z ≠ 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ball z₀ r ⊆ U ∧ ∃ X : ℂ → Fin 3 → ℝ,
      X z₀ = 0 ∧ AnalyticOnNhd ℝ X (ball z₀ r) ∧ HarmonicOnNhd X (ball z₀ r) ∧
      ∀ z ∈ ball z₀ r,
        fderiv ℝ X z = nullRealDerivative (Φ z) ∧ Function.Injective (fderiv ℝ X z) ∧
        0 < nullMetric (Φ z) ∧
        (∑ j, (fderiv ℝ X z 1 j)^2) = nullMetric (Φ z) ∧
        (∑ j, (fderiv ℝ X z I j)^2) = nullMetric (Φ z) ∧
        (∑ j, fderiv ℝ X z 1 j*fderiv ℝ X z I j) = 0 := by
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz₀)
  have hd : DifferentiableOn ℂ Φ (ball z₀ r) :=
    fun z hz => (hΦ z (hrU hz)).differentiableAt.differentiableWithinAt
  obtain ⟨F,hF₀,hF⟩ := hd.isExactOn_ball.with_val_at z₀ 0
  have hFa : AnalyticOnNhd ℂ F (ball z₀ r) :=
    (show DifferentiableOn ℂ F (ball z₀ r) from
      fun z hz => (hF z hz).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball
  refine ⟨r,hr,hrU,(fun w => coordinateRealPart (F w)),?_,?_,?_,?_⟩
  · change coordinateRealPart (F z₀) = 0
    rw [hF₀,map_zero]
  · intro z hz
    exact (coordinateRealPart.analyticAt (F z)).comp ((hFa z hz).restrictScalars (𝕜 := ℝ))
  · intro z hz
    exact (hFa z hz).harmonicAt.comp_CLM coordinateRealPart
  · intro z hz
    have he := (realPart_primitive_hasFDerivAt (hF z hz)).fderiv
    refine ⟨he,?_,?_⟩
    · rw [he]
      exact nullRealDerivative_injective (hnull z (hrU hz)) (hn z (hrU hz))
    · rw [he]
      exact nullRealDerivative_conformal (hnull z (hrU hz)) (hn z (hrU hz))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.holomorphic_null_local_immersion
