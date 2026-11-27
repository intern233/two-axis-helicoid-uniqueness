import TwoAxisHelicoid.MarkedHolomorphicFilling
import TwoAxisHelicoid.MarkedArbitraryGraphRigidity
import TwoAxisHelicoid.ReferenceFrameHarmonic
import TwoAxisHelicoid.ClassicalRiemannUniformizationSpecialization
import TwoAxisHelicoid.HelicoidAnnularCompactification
import TwoAxisHelicoid.OriginalHelicoidRepresentative

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology ContDiff Manifold

universe u

/-- From just the filled complex structure and the physical C¹ end the
original finite surface, at arbitrary pitch and horizontal line, is
positively similar point by point to the certified immersion. -/
theorem filled_graph_surface_certified {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (uniform : CompactGenusOneUniformization.{u} L₀) (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e) (E : PuncturedComplexEnd M)
    (hol : E.coord∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) (axes : OriginalHelicoidAxes (range X))
    (graph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization axes.pitch_ne ![0,0,0] ∘ X)) :
    ∃ (f : M ≃ₜ PuncturedPeriodTorus certifiedPeriodPair) (k : ℝ)
      (A : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)), 0<k ∧
      ∀ x, certifiedTorusImmersion (f x)=k • A (coordinateToEuclidean (X x)) := by
  obtain ⟨L,U,Y,_,_,pos,cl,im,reg⟩ := marked_harmonic_torus_of_filling top uniform X closed charts E hol
  let R := axisSpatialNormalization axes.pitch_ne ![0,0,0]
  let Y' := R ∘ Y
  have image : range (fun q : PuncturedPeriodTorus L => Y' q.1)=R '' range X := by
    rw [← im,← range_comp]
    rfl
  obtain ⟨line,axis⟩ := reference_frame_maps_straight_axes axes.pitch_ne axes.horizontalDirection axes.horizontalPoint axes.horizontal axes.vertical
  have regular (z : ℂ) (hz : z∉L.lattice) := reference_frame_harmonic_chart (reg z hz).1 (reg z hz).2.1 (reg z hz).2.2 axes.pitch_ne
  have e : (coordinateToTube ∘ R ∘ X) ∘ U.symm=(fun q : PuncturedPeriodTorus L => coordinateToTube (Y' q.1)) := by
    funext q
    change coordinateToTube (R (X (U.symm q)))=coordinateToTube (R (Y q.1))
    rw [← pos (U.symm q),U.apply_symm_apply]
  have hg := e ▸ graph.comp_homeomorph U.symm
  obtain ⟨V,k,B,b,hk,eq⟩ := marked_arbitrary_horizontal_graph_similarity L Y' (R.isClosedEmbedding.comp cl)
    axes.horizontalDirection axes.unit (R axes.horizontalPoint) (image.symm ▸ line) (image.symm ▸ axis) regular hg
  obtain ⟨T,hT⟩ := reference_frame_euclidean_dilation axes.pitch_ne
  let Q := (T.trans B.toDilationEquiv).trans (DilationEquiv.smulTorsor b hk.ne')
  obtain ⟨s,A,hs,ha⟩ := dilation_eq_positive_smul_isometry Q
  refine ⟨U.trans V,s,A,hs,fun x => (eq (U x)).trans ?_⟩
  rw [← ha]
  change k • B (coordinateToEuclidean (R (Y (U x).1)))+b=k • B (T (coordinateToEuclidean (X x)))+b
  rw [pos,hT]

/-- An actual isothermal annulus marking the given physical end is
enough. Its modulus, conformal puncture, both poles and full torus
model follow from the graph. -/
theorem annular_graph_surface_certified {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (uniform : CompactGenusOneUniformization.{u} L₀) (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e) (axes : OriginalHelicoidAxes (range X))
    (graph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization axes.pitch_ne ![0,0,0] ∘ X))
    (e : OpenPartialHomeomorph M ℂ) (hol : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    (iso : InducedIsothermalChart (axisSpatialNormalization axes.pitch_ne ![0,0,0] ∘ X) e)
    {r R : ℝ} (hr : 0≤r) (hR : r<R) (target : e.target={z : ℂ | r<‖z‖ ∧ ‖z‖<R})
    (core : IsCompact e.sourceᶜ) (radius : Filter.Tendsto (fun x => ‖e x‖) (Filter.cocompact M) (𝓝 r)) :
    ∃ (f : M ≃ₜ PuncturedPeriodTorus certifiedPeriodPair) (k : ℝ)
      (A : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)), 0<k ∧
      ∀ x, certifiedTorusImmersion (f x)=k • A (coordinateToEuclidean (X x)) := by
  let := punctured_complex_curve_noncompact (0:PeriodTorus L₀)
  let : NoncompactSpace M := ⟨fun h => noncompact_univ (PuncturedPeriodTorus L₀) (by
    simpa only [image_univ,top.surjective.range_eq] using h.image top.continuous)⟩
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ℂ M
  let N := axisSpatialNormalization axes.pitch_ne ![0,0,0]
  have hc : IsClosedEmbedding (N ∘ X) := N.isClosedEmbedding.comp closed
  obtain ⟨_,E,eq,_⟩ := helicoid_annular_chart_fills hc.isProperMap hc.injective graph e iso hr hR target core radius
  exact filled_graph_surface_certified top uniform X closed charts E (eq ▸ hol) axes graph

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.annular_graph_surface_certified
