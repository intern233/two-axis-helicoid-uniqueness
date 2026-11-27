import TwoAxisHelicoid.PhysicalGraphPunctureFilling
import TwoAxisHelicoid.OriginalC1GraphPuncturePoles
import TwoAxisHelicoid.OriginalRealMorseIndex

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology TopologicalSpace
open scoped Topology ContDiff Manifold

universe u

/-- The classical classification of doubly connected Riemann surfaces,
stated on an arbitrary surface with the topology of an open annulus. -/
def AnnularRiemannSurfaceUniformization : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    (R : ℝ), 0<R → Nonempty (M ≃ₜ {z : ℂ // 0<‖z‖ ∧ ‖z‖<R}) →
    ∃ T : Opens ℂ, IsRoundCylinderTarget T ∧ Nonempty (Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) M T ω)

theorem annular_classification_of_plane_uniformization (uni : TopologicalPlaneUniformization.{u}) :
    AnnularRiemannSurfaceUniformization.{u} :=
  fun _ _ _ _ _ hr ⟨mark⟩ => annular_uniformization_of_plane_dichotomy hr mark uni

/-- The conformal type of the single physical end is determined using
only the classification of its annular neighborhood. Its finite-modulus
alternative is ruled out by the geometry of the normal graph. -/
theorem physical_graph_filling_of_annular_classification {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [NoncompactSpace M]
    {X : M → Fin 3 → ℝ} (emb : IsClosedEmbedding X) (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (graph : HasHelicoidC1End (coordinateToTube ∘ X)) (ann : AnnularRiemannSurfaceUniformization.{u}) :
    ∃ E : PuncturedComplexEnd M, E.coord∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M := by
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ℂ M
  obtain ⟨D,_⟩ := graph.natural_puncture_coordinate (coordinateToTube_isProperMap emb.isProperMap)
  let S : Opens M := ⟨D.coord.source,D.coord.open_source⟩
  have target : D.coord.target={z : ℂ | 0<‖z‖ ∧ ‖z‖<D.radius} := by
    rw [D.target_eq]
    ext z
    change (dist z 0<D.radius ∧ z≠0) ↔ 0<‖z‖ ∧ ‖z‖<D.radius
    rw [dist_zero_right,norm_pos_iff,and_comm]
  let marking : S ≃ₜ {z : ℂ // 0<‖z‖ ∧ ‖z‖<D.radius} :=
    D.coord.toHomeomorphSourceTarget.trans (Homeomorph.setCongr target)
  have half := half_pos D.radius_pos
  have size : ‖((D.radius/2:ℝ):ℂ)‖=D.radius/2 := by rw [Complex.norm_real,Real.norm_of_nonneg half.le]
  have non : Nonempty S := ⟨marking.symm ⟨(D.radius/2:ℝ),by rw [size]; exact ⟨half,half_lt_self D.radius_pos⟩⟩⟩
  obtain ⟨T,round,⟨U⟩⟩ := ann S D.radius D.radius_pos ⟨marking⟩
  obtain ⟨c,src,tgt,cm⟩ := holomorphic_subdomain_coordinate S T non U
  obtain ⟨e,r,R,hr,lt,hol,compact,image,radius⟩ := one_ended_round_chart_collar D.connected_tails c
    (by rw [src]; exact D.compact_core) cm (by rw [tgt]; exact round)
  have harm := harmonic_immersion_chart_maximal charts hol
  have iso : InducedIsothermalChart X e :=
    ⟨fun z hz => ⟨(analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt ((harm z hz).1 j))).contDiffAt,
      (harm z hz).2.2⟩,fun z hz => (harm z hz).2.1⟩
  obtain ⟨_,E,eq,_⟩ := helicoid_annular_chart_fills emb.isProperMap emb.injective graph e iso hr lt image compact radius
  exact ⟨E,eq ▸ hol⟩

/-- For the physical two-axis C¹ class the punctured chart, the two
actual meromorphic poles and the zero-normalized Weierstrass exterior
are determined before any conformal identification of the handle. -/
theorem original_graph_exterior_of_annular_classification {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [ConnectedSpace M] [NoncompactSpace M]
    {X : M → Fin 3 → ℝ} (emb : IsClosedEmbedding X) (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (axes : OriginalHelicoidAxes (range X))
    (graph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization axes.pitch_ne ![0,0,0] ∘ X))
    (ann : AnnularRiemannSurfaceUniformization.{u}) :
    ∃ E : PuncturedComplexEnd M, E.coord∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M ∧
      (let Y := X ∘ E.coord.symm
       (MeromorphicAt (fun z => immersionComplexCoefficient Y z 2) 0 ∧ meromorphicOrderAt (fun z => immersionComplexCoefficient Y z 2) 0=(-2:ℤ)) ∧
       MeromorphicAt (immersionGaussLogDerivative Y) 0 ∧ meromorphicOrderAt (immersionGaussLogDerivative Y) 0=(-2:ℤ)) ∧
      ∃ G : GeometricExteriorCoordinate X, G.correction 0=0 := by
  let R := axisSpatialNormalization axes.pitch_ne ![0,0,0]
  have normalized : ∀ e∈atlas ℂ M, HarmonicImmersionChart (R ∘ X) e :=
    fun e he z hz => reference_frame_harmonic_chart (charts e he z hz).1 (charts e he z hz).2.1 (charts e he z hz).2.2 axes.pitch_ne
  obtain ⟨E,hol⟩ := physical_graph_filling_of_annular_classification (R.isClosedEmbedding.comp emb) normalized graph ann
  exact ⟨E,hol,physical_two_axis_graph_orders_in_given_puncture emb charts axes graph E hol,
    original_C1_exterior_from_conformal_puncture emb charts axes graph E hol⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.physical_graph_filling_of_annular_classification
#print axioms TwoAxisHelicoid.original_graph_exterior_of_annular_classification
