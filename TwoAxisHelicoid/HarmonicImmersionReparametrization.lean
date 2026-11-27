import TwoAxisHelicoid.HarmonicComplexCoefficient

namespace TwoAxisHelicoid
open Complex Metric Filter InnerProductSpace
open scoped Topology

/-- Real harmonic coordinates remain harmonic under any local holomorphic
parameter, by composing their actual local holomorphic primitives. -/
theorem harmonic_scalar_comp_analytic {f : ℂ → ℝ} {u : ℂ → ℂ} {z : ℂ}
    (hf : HarmonicAt f (u z)) (hu : AnalyticAt ℂ u z) : HarmonicAt (f ∘ u) z := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp ((isOpen_setOfPred_harmonicAt (f := f)).mem_nhds hf)
  have hH : HarmonicOnNhd f (ball (u z) r) := fun w hw => hball hw
  obtain ⟨F,hF,he⟩ := hH.exists_analyticOnNhd_ball_re_eq
  apply (harmonicAt_congr_nhds (f₂ := reCLM ∘ (F ∘ u)) ?_).mpr
  · exact ((hF _ (mem_ball_self hr)).comp hu).harmonicAt.comp_CLM reCLM
  · filter_upwards [hu.continuousAt.eventually (ball_mem_nhds _ hr)] with w hw
    exact (he hw).symm

/-- The regular, conformal, harmonic conditions on the actual three
coordinates are invariant under an arbitrary regular holomorphic parameter. -/
theorem harmonic_immersion_reparametrization {X : ℂ → Fin 3 → ℝ} {u : ℂ → ℂ} {z : ℂ}
    (hh : ∀ j, HarmonicAt (fun w => X w j) (u z)) (hc : ConformalCoordinateDerivatives X (u z))
    (hi : Function.Injective (fderiv ℝ X (u z))) (hu : AnalyticAt ℂ u z) (hne : deriv u z ≠ 0) :
    (∀ j, HarmonicAt (fun w => (X ∘ u) w j) z) ∧ ConformalCoordinateDerivatives (X ∘ u) z ∧
      Function.Injective (fderiv ℝ (X ∘ u) z) := by
  let d := deriv u z
  let p := immersionComplexCoefficient X (u z)
  let q := fun j => d * p j
  have hX : DifferentiableAt ℝ X (u z) :=
    (analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (hh j))).differentiableAt
  have hp : ComplexNull p := immersionComplexCoefficient_null hc
  have hq : ComplexNull q := by
    dsimp [ComplexNull,q] at *
    linear_combination d^2 * hp
  have hn : q ≠ 0 := by
    intro h
    apply immersionComplexCoefficient_regular hX hi
    ext j
    exact (mul_eq_zero.mp (show d * p j = 0 from congrFun h j)).resolve_left hne
  have hd := (immersionComplexCoefficient_hasFDerivAt hX).comp z
    (hu.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ)
  have hD : HasFDerivAt (X ∘ u) (nullRealDerivative q) z := by
    convert hd using 1
    ext w j
    change (w*(d*p j)).re = ((w*d)*p j).re
    rw [mul_assoc]
  obtain ⟨_,h1,hI,hperp⟩ := nullRealDerivative_conformal hq hn
  have hcomp (j : Fin 3) : fderiv ℝ (fun w => (X ∘ u) w j) z =
      (ContinuousLinearMap.proj j).comp (nullRealDerivative q) :=
    ((ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z hD).fderiv
  refine ⟨fun j => harmonic_scalar_comp_analytic (hh j) hu,?_,?_⟩
  · unfold ConformalCoordinateDerivatives
    simpa only [hcomp,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply] using And.intro (h1.trans hI.symm) hperp
  · rw [hD.fderiv]
    exact nullRealDerivative_injective hq hn

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_immersion_reparametrization
