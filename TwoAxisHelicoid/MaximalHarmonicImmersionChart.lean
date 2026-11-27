import TwoAxisHelicoid.HarmonicExteriorCoordinates
import TwoAxisHelicoid.HarmonicImmersionReparametrization
import TwoAxisHelicoid.NullGaussLogSymmetry
import TwoAxisHelicoid.HolomorphicImmersionCoordinateChange

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- A change between two holomorphic surface charts has a nonvanishing
ordinary complex derivative at every point where the change is defined. -/
theorem holomorphic_transition_deriv_ne_zero {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {e d : OpenPartialHomeomorph M ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) {z : ℂ} (hz : z ∈ (e.symm.trans d).source) :
    deriv (e.symm.trans d) z ≠ 0 := by
  let f := e.symm.trans d
  have h₁ := (complexAtlas_realized_transition he hd hz).analyticAt.differentiableAt
  have h₂ : DifferentiableAt ℂ f.symm (f z) :=
    (complexAtlas_realized_transition hd he (f.map_source hz)).analyticAt.differentiableAt
  have heq : f.symm ∘ f =ᶠ[𝓝 z] id := by
    filter_upwards [f.open_source.mem_nhds hz] with w hw
    exact f.left_inv hw
  have hder : deriv f.symm (f z)*deriv f z = 1 :=
    (deriv_comp z h₂ h₁).symm.trans (heq.deriv_eq.trans (deriv_id z))
  exact fun h => by change deriv f z = 0 at h; simp [h] at hder

/-- A regular harmonic conformal immersion in the preferred atlas has
these same three properties in every compatible holomorphic chart. -/
theorem harmonic_immersion_chart_maximal {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {X : M → Fin 3 → ℝ} (hX : ∀ d ∈ atlas ℂ M, HarmonicImmersionChart X d)
    {e : OpenPartialHomeomorph M ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) :
    HarmonicImmersionChart X e := by
  intro z hz
  let d := chartAt ℂ (e.symm z)
  let u := e.symm.trans d
  have hd : d ∈ atlas ℂ M := chart_mem_atlas ℂ _
  have hsrc : z ∈ u.source := ⟨hz,mem_chart_source ℂ _⟩
  have hu := (complexAtlas_realized_transition he (IsManifold.subset_maximalAtlas hd) hsrc).analyticAt
  have hn := holomorphic_transition_deriv_ne_zero he (IsManifold.subset_maximalAtlas hd) hsrc
  obtain ⟨hh,hc,hr⟩ := hX d hd (u z) (d.map_source hsrc.2)
  obtain ⟨hh',hc',hr'⟩ := harmonic_immersion_reparametrization hh hc hr hu hn
  have heq : (X ∘ e.symm) =ᶠ[𝓝 z] (X ∘ d.symm) ∘ u := by
    filter_upwards [u.open_source.mem_nhds hsrc] with w hw
    exact congrArg X (d.left_inv hw.2).symm
  have hD : DifferentiableAt ℝ ((X ∘ d.symm) ∘ u) z :=
    (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (hh' j)).differentiableAt
  refine ⟨fun j => (harmonicAt_congr_nhds (heq.fun_comp (fun A => A j))).mpr (hh' j),?_,?_⟩
  · apply (conformalCoordinateDerivatives_iff_dot (hD.congr_of_eventuallyEq heq)).mpr
    rw [heq.fderiv_eq (𝕜 := ℝ)]
    exact (conformalCoordinateDerivatives_iff_dot hD).mp hc'
  · rw [heq.fderiv_eq (𝕜 := ℝ)]
    exact hr'

/-- A pole of the true height coefficient excludes vertical Gauss chart
singularities on a deleted neighborhood, using the actual null equation. -/
theorem height_pole_implies_regular_gauss_germ {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : ∀ᶠ w in 𝓝[≠] z, (∀ j, HarmonicAt (fun v => X v j) w) ∧ ConformalCoordinateDerivatives X w)
    (hh : MeromorphicAt (fun w => immersionComplexCoefficient X w 2) z)
    (hn : meromorphicOrderAt (fun w => immersionComplexCoefficient X w 2) z ≠ ⊤) :
    ∀ᶠ w in 𝓝[≠] z, DifferentiableAt ℝ X w ∧ DifferentiableAt ℂ (immersionGaussMap X) w := by
  filter_upwards [hX,(meromorphicOrderAt_ne_top_iff_eventually_ne_zero hh).mp hn] with w hw hne
  have ha (j : Fin 3) : AnalyticAt ℂ (fun v => immersionComplexCoefficient X v j) w :=
    scalarComplexCoefficient_analyticAt (hw.1 j)
  exact ⟨(analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (hw.1 j))).differentiableAt,
    (nullGauss_analyticAt_of_height ha (immersionComplexCoefficient_null hw.2) hne).differentiableAt⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_immersion_chart_maximal
#print axioms TwoAxisHelicoid.height_pole_implies_regular_gauss_germ
