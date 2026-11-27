import TwoAxisHelicoid.ConformalMinimalHarmonic
import TwoAxisHelicoid.HarmonicNullLift

namespace TwoAxisHelicoid
open Complex Matrix Filter Set InnerProductSpace
open scoped Topology ComplexConjugate

theorem fderiv_real_coordinate {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : DifferentiableAt ℝ X z) (j : Fin 3) (v : ℂ) :
    fderiv ℝ (fun w => X w j) z v = fderiv ℝ X z v j := by
  have h := ((ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp
    z hX.hasFDerivAt).fderiv
  exact congrArg (fun D : ℂ →L[ℝ] ℝ => D v) h

theorem conformalCoordinateDerivatives_iff_dot {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : DifferentiableAt ℝ X z) :
    ConformalCoordinateDerivatives X z ↔
      fderiv ℝ X z 1 ⬝ᵥ fderiv ℝ X z 1 = fderiv ℝ X z I ⬝ᵥ fderiv ℝ X z I ∧
      fderiv ℝ X z 1 ⬝ᵥ fderiv ℝ X z I = 0 := by
  simp only [ConformalCoordinateDerivatives,dotProduct,fderiv_real_coordinate hX,pow_two]

theorem conformal_minimal_chart_harmonicAt {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : ContDiffAt ℝ 2 X z)
    (hc : ∀ᶠ w in 𝓝 z, ConformalCoordinateDerivatives X w)
    (hi : ∀ᶠ w in 𝓝 z, Function.Injective (fderiv ℝ X w))
    (hm : ∀ᶠ w in 𝓝 z, coordinateMeanCurvature X w = 0) : HarmonicAt X z := by
  apply conformal_minimal_harmonicAt hX ?_ hi hm
  filter_upwards [hX.eventually (by norm_num),hc] with w hw hcw
  exact (conformalCoordinateDerivatives_iff_dot (hw.differentiableAt two_ne_zero)).mp hcw

/-- The actual derivative of an arbitrary regular C² minimal conformal
chart gives holomorphic nonzero null coefficients. This is a necessary
representation theorem, not a construction from preassigned data. -/
theorem minimal_chart_actual_complex_data {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : ContDiffAt ℝ 2 X z)
    (hc : ∀ᶠ w in 𝓝 z, ConformalCoordinateDerivatives X w)
    (hi : ∀ᶠ w in 𝓝 z, Function.Injective (fderiv ℝ X w))
    (hm : ∀ᶠ w in 𝓝 z, coordinateMeanCurvature X w = 0) :
    (∀ j, AnalyticAt ℂ (fun w => immersionComplexCoefficient X w j) z) ∧
      ComplexNull (immersionComplexCoefficient X z) ∧
      immersionComplexCoefficient X z ≠ 0 ∧
      HasFDerivAt X (nullRealDerivative (immersionComplexCoefficient X z)) z := by
  have hh := conformal_minimal_chart_harmonicAt hX hc hi hm
  refine ⟨?_,immersionComplexCoefficient_null hc.self_of_nhds,
    immersionComplexCoefficient_regular (hX.differentiableAt two_ne_zero) hi.self_of_nhds,
    immersionComplexCoefficient_hasFDerivAt (hX.differentiableAt two_ne_zero)⟩
  intro j
  exact scalarComplexCoefficient_analyticAt
    (hh.comp_CLM (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ))

/-- For an actual map already placed in the punctured lattice coordinate,
geometric minimality can replace the previous harmonicity input. The
existence of that conformal coordinate and the end pole orders are not
asserted here. -/
theorem two_axis_harmonic_of_minimal {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : ∀ z ∉ L.lattice, ContDiffAt ℝ 2 X z)
    (hc : ∀ z ∉ L.lattice, ConformalCoordinateDerivatives X z)
    (hi : ∀ z ∉ L.lattice, Function.Injective (fderiv ℝ X z))
    (hm : ∀ z ∉ L.lattice, coordinateMeanCurvature X z = 0)
    (hp : ∀ z ∉ L.lattice, ∀ ω ∈ L.lattice, X (z+ω) = X z)
    (hn : ∀ z ∉ L.lattice, X (-z) = ![-X z 0,X z 1,-X z 2])
    (hr : ∀ z ∉ L.lattice, X (conj z) = ![X z 0,-X z 1,-X z 2]) :
    TwoAxisHarmonicConformalImmersion L X where
  differentiable := fun z hz => (hX z hz).differentiableAt two_ne_zero
  harmonic := by
    intro z hz j
    have hne := L.isClosed_lattice.isOpen_compl.mem_nhds hz
    have hh := conformal_minimal_chart_harmonicAt (hX z hz)
      (Filter.Eventually.mono hne (fun w hw => hc w hw))
      (Filter.Eventually.mono hne (fun w hw => hi w hw))
      (Filter.Eventually.mono hne (fun w hw => hm w hw))
    exact hh.comp_CLM (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ)
  conformal := hc
  immersion := hi
  periodic := hp
  neg := hn
  conjugation := hr

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.minimal_chart_actual_complex_data
#print axioms TwoAxisHelicoid.two_axis_harmonic_of_minimal
