import TwoAxisHelicoid.MultiplierLineSections
import TwoAxisHelicoid.MultiplierUnitFiber
import TwoAxisHelicoid.PeriodTorusComplexManifold
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped TensorProduct Topology Manifold
set_option maxHeartbeats 1000000

/-- The actual compact-torus chart transition identifies cotangent
coefficients by the identity. Its complex derivative is obtained from
its genuine local lattice translation. -/
theorem torus_chart_transition_complex_derivative (L : PeriodPair)
    (e e' : OpenPartialHomeomorph (PeriodTorus L) ℂ)
    (he : (e.symm : ℂ → PeriodTorus L) = periodTorusProjection L)
    (he' : (e'.symm : ℂ → PeriodTorus L) = periodTorusProjection L)
    {z : ℂ} (hz : z ∈ (e.symm.trans e').source) :
    HasFDerivAt (e.symm.trans e') (ContinuousLinearMap.id ℂ ℂ) z := by
  exact ((hasFDerivAt_id z).add_const ((e.symm.trans e') z-z)).congr_of_eventuallyEq
    (periodTorus_chart_transition_translation L e e' he he' hz)

/-- The chosen quotient chart, evaluated at any plane lift of its
center, differs from the identity by a fixed lattice period nearby. -/
theorem period_torus_projection_chart_translate (L : PeriodPair) (z : ℂ) :
    ∃ ω : L.lattice, ∀ᶠ w in 𝓝 z,
      chartAt ℂ (periodTorusProjection L z) (periodTorusProjection L w) = w+ω.1 := by
  let q := periodTorusProjection L z
  let e' := chartAt ℂ q
  obtain ⟨j,hz,hj⟩ := periodTorusProjection_isLocalHomeomorph L z
  have hjz : j z = q := (congrFun hj z).symm
  have hsource : z ∈ (j.trans e').source := ⟨hz,by change j z ∈ e'.source; rw [hjz]; exact mem_chart_source ℂ q⟩
  have hω := periodTorus_chart_transition_lattice L j.symm e' hj.symm
    (periodTorus_chart_symm_eq_projection L q) hsource
  refine ⟨⟨_,hω⟩,?_⟩
  have h := periodTorus_chart_transition_translation L j.symm e' hj.symm
    (periodTorus_chart_symm_eq_projection L q) hsource
  filter_upwards [h] with w hw
  change e' (j w) = _ at hw
  rw [← hj] at hw
  exact hw

/-- In the genuine manifold tangent spaces the covering projection has
identity derivative at every lift. -/
theorem period_torus_projection_has_complex_mfderiv (L : PeriodPair) (z : ℂ) :
    HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (periodTorusProjection L) z (ContinuousLinearMap.id ℂ ℂ) := by
  obtain ⟨ω,hω⟩ := period_torus_projection_chart_translate L z
  have hd : HasFDerivAt (chartAt ℂ (periodTorusProjection L z) ∘ periodTorusProjection L)
      (ContinuousLinearMap.id ℂ ℂ) z := ((hasFDerivAt_id z).add_const ω.1).congr_of_eventuallyEq hω
  refine ⟨QuotientAddGroup.continuous_mk.continuousAt,?_⟩
  simpa only [writtenInExtChartAt,mfld_simps] using! hd.hasFDerivWithinAt (s := range 𝓘(ℂ))

theorem period_torus_projection_complex_analytic (L : PeriodPair) (z : ℂ) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (periodTorusProjection L) z := by
  obtain ⟨ω₀,hω⟩ := period_torus_projection_chart_translate L z
  have hd : AnalyticAt ℂ (chartAt ℂ (periodTorusProjection L z) ∘ periodTorusProjection L) z :=
    (analyticAt_id.add (analyticAt_const (v := ω₀.1))).congr (Filter.EventuallyEq.symm hω)
  apply contMDiffAt_iff.mpr
  refine ⟨QuotientAddGroup.continuous_mk.continuousAt,?_⟩
  simpa only [mfld_simps] using! hd.contDiffAt.contDiffWithinAt (s := range 𝓘(ℂ)) (n := ω)

/-- The coordinate change of the multiplier line is locally its actual
lattice sign on every overlap in the compact torus complex atlas. -/
theorem multiplier_line_chart_change (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (S : MultiplierLineSection L χ) (e e' : OpenPartialHomeomorph (PeriodTorus L) ℂ)
    (he : (e.symm : ℂ → PeriodTorus L) = periodTorusProjection L)
    (he' : (e'.symm : ℂ → PeriodTorus L) = periodTorusProjection L)
    {z : ℂ} (hz : z ∈ (e.symm.trans e').source) :
    ∃ ω : L.lattice, (e.symm.trans e') z-z = ω.1 ∧
      ∀ᶠ w in 𝓝 z, multiplierSectionPlane L χ S ((e.symm.trans e') w) =
        paritySign (χ ω)*multiplierSectionPlane L χ S w := by
  let ω : L.lattice := ⟨_,periodTorus_chart_transition_lattice L e e' he he' hz⟩
  refine ⟨ω,rfl,?_⟩
  filter_upwards [periodTorus_chart_transition_translation L e e' he he' hz] with w hw
  rw [hw]
  exact multiplierSectionPlane_translate L χ S w ω

abbrev TorusCanonicalFiber (L : PeriodPair) (q : PeriodTorus L) :=
  TangentSpace 𝓘(ℂ) q →L[ℂ] ℂ

/-- The coefficient is now sent to an actual complex covector on the
compact complex manifold, rather than just to a scalar. -/
noncomputable def multiplierCanonicalSquare (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (q : PeriodTorus L) (e : SignFiber L χ q) :
    (multiplierLineFiber L χ q ⊗[ℂ] multiplierLineFiber L χ q) ≃ₗ[ℂ] TorusCanonicalFiber L q :=
  (multiplierTensorSquare L χ q e).trans (ContinuousLinearMap.toSpanSingletonLE ℂ ℂ ℂ)

theorem multiplierCanonicalSquare_independent (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (q : PeriodTorus L) (e d : SignFiber L χ q) :
    multiplierCanonicalSquare L χ q e = multiplierCanonicalSquare L χ q d := by
  rw [multiplierCanonicalSquare,multiplierCanonicalSquare,multiplierTensorSquare_independent L χ q e d]

/-- Pulling the tensor square of two spin vectors to the universal cover
by the actual manifold derivative gives their product times dz. -/
theorem multiplierCanonicalSquare_pullback (L : PeriodPair) (χ : L.lattice →+ ZMod 2) (z : ℂ)
    (e : SignFiber L χ (periodTorusProjection L z)) (v w : multiplierLineFiber L χ (periodTorusProjection L z)) (ξ : ℂ) :
    multiplierCanonicalSquare L χ _ e (v ⊗ₜ w)
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) (periodTorusProjection L) z ξ) = v.1 e*w.1 e*ξ := by
  rw [(period_torus_projection_has_complex_mfderiv L z).mfderiv]
  change ξ*(v.1 e*w.1 e) = _
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.period_torus_projection_has_complex_mfderiv
#print axioms TwoAxisHelicoid.multiplier_line_chart_change
#print axioms TwoAxisHelicoid.multiplierCanonicalSquare_pullback
