import TwoAxisHelicoid.MarkedAtlasPhysicalExterior
import TwoAxisHelicoid.UnmarkedFiniteTopologyGeometry
import TwoAxisHelicoid.FixedMarkedExteriorRigidity

namespace TwoAxisHelicoid
open Complex Set Topology Filter InnerProductSpace
open scoped Topology ContDiff Manifold

/-- Rigidity on the given marked domain: a nonvertical flux, the exact
first-order multiplier test, and rotation-translation of every competing
immersion with the same data or the same full Laurent principal parts. -/
def FixedMarkedCoordinateRigidity (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ) : Prop :=
    (∃ (q : PuncturedPeriodTorus L) (γ : Path q q) (j : Fin 3) (v : ℝ),
      j≠2 ∧ v≠0 ∧ TorusSpatialConormalIntegral L X j γ v) ∧
    (∀ {k : ℝ → ℂ} {d : ℂ}, HasDerivAt k d 0 → k 0=1 → (LopezRosClosedToFirstOrder L X k ↔ d.re=0)) ∧
    ∀ Y : PuncturedPeriodTorus L → Fin 3 → ℝ,
    (∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Y w j) z) ∧ ConformalCoordinateDerivatives (puncturedTorusPullback L Y) z) →
    (((∀ z ∉ L.lattice, torusImmersionForms L Y z 2=torusImmersionForms L X z 2) ∧
      (∀ z ∉ L.lattice, torusImmersionForms L X z 2≠0 →
        immersionGaussLog (torusImmersionForms L Y) z=immersionGaussLog (torusImmersionForms L X) z)) ∨
     (CommonLaurentPartAt (fun z => torusImmersionForms L X z 2) (fun z => torusImmersionForms L Y z 2) 0 ∧
       ∀ z, CommonLaurentPartAt (immersionGaussLog (torusImmersionForms L X)) (immersionGaussLog (torusImmersionForms L Y)) z)) →
    ∃ (θ : ℝ) (b : Fin 3 → ℝ), (∀ q, Y q=verticalRotation (exp ((θ:ℂ)*I)) (X q)+b) ∧
      ∀ q, torusSphericalGauss L Y q=OnePoint.map (exp ((θ:ℂ)*I)*·) (torusSphericalGauss L X q)

/-- C.4 and C.5 on the original marked torus with a single physical C¹
graph, allowing every nonzero signed pitch. -/
theorem fixed_marked_graph_flux_and_rigidity (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (cl : IsClosedEmbedding X) (charts : ∀ e∈atlas ℂ (PuncturedPeriodTorus L), HarmonicImmersionChart X e)
    {α : ℝ} (ha : α≠0) (graph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization ha ![0,0,0] ∘ X)) :
    MarkedHelicoidalEndForms L X ∧ FixedMarkedCoordinateRigidity L X := by
  obtain ⟨A,_⟩ := fixed_marked_graph_has_normalized_exterior L X cl charts ha graph
  exact ⟨fixed_marked_exterior_has_end_forms L X cl charts A,fixed_marked_exterior_flux_and_rigidity L X cl charts A⟩

/-- In the weaker positional definition, the sole external input here
is the general scalar Gaussian-curvature bound for complete embedded
finite-topology minimal surfaces. -/
theorem fixed_marked_positional_flux_and_rigidity (mp : PublishedFiniteTopologyGaussianCurvature)
    (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ) (cl : IsClosedEmbedding X)
    (charts : ∀ e∈atlas ℂ (PuncturedPeriodTorus L), HarmonicImmersionChart X e)
    {α : ℝ} (ha : α≠0) (pos : ApproachesSetAtInfinity (range X) (range (axisRuledHelicoid I α 0))) :
    MarkedHelicoidalEndForms L X ∧ FixedMarkedCoordinateRigidity L X := by
  have reg := marked_punctured_atlas_pullback_regular L X charts
  have hh := fun z hz => (reg z hz).1
  have sm := (harmonic_marked_torus_contMDiff L X hh).of_le (show (∞ : WithTop ℕ∞)≤ω by simp)
  have di (q : PuncturedPeriodTorus L) : Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X q) := by
    rw [(harmonic_marked_torus_hasMFDerivAt L X hh q).mfderiv]
    exact (reg _ (puncturedPeriodTorus_chart_not_lattice L q)).2.2
  have minimal (q : PuncturedPeriodTorus L) : coordinateMeanCurvature (X ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q)=0 := by
    let e := chartAt ℂ q
    obtain ⟨h,c,_⟩ := charts e (chart_mem_atlas ℂ q) (e q) (e.map_source (mem_chart_source ℂ q))
    have harmonic := spatial_harmonic_of_coordinates h
    obtain ⟨len,orth⟩ := (conformalCoordinateDerivatives_iff_dot (harmonic.1.differentiableAt two_ne_zero)).mp c
    exact conformal_harmonic_coordinate_mean_curvature_zero harmonic rfl len.symm orth
  let f := Homeomorph.refl (PuncturedPeriodTorus L)
  obtain ⟨C,cn,bound⟩ := gaussian_bound_for_punctured_handle mp f X cl sm di minimal
  have graph := one_ended_positional_graph_of_gaussian_bound X cl sm di minimal (punctured_handle_connected_tails f)
    isCompact_empty cn (fun q _ => bound q) ha pos
  exact fixed_marked_graph_flux_and_rigidity L X cl charts ha graph

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.fixed_marked_graph_flux_and_rigidity
#print axioms TwoAxisHelicoid.fixed_marked_positional_flux_and_rigidity
