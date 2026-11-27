import TwoAxisHelicoid.FiniteOneEndGeometricPublication
import TwoAxisHelicoid.ExteriorOnePointPoleModel
import TwoAxisHelicoid.PublishedGeometricClassification
import TwoAxisHelicoid.OriginalSurfaceMorseIndex

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold

theorem HasSinglePuncturedSurfaceTopology.connected_tails {M : Type} [TopologicalSpace M]
    (top : HasSinglePuncturedSurfaceTopology M) : HasConnectedCompactTails M := by
  obtain ⟨K,t,sep,compact,_,⟨ch⟩,p,⟨f⟩⟩ := top
  let _ := t
  let _ := sep
  let _ := compact
  let _ := ch
  exact homeomorphic_punctured_surface_connected_tails p f

/-- Proposition 2.1 for arbitrary finite genus. The published geometric
input supplies a differential on the end. Lean constructs the compact
model and verifies the exact two pole orders of the physical map, then
integrates and normalizes the exponential Gauss correction. -/
theorem finite_one_ended_surface_conformal_poles_and_normalized_end
    (bbc : PublishedFiniteOneEndDifferentialGeometry) {M : Type} [TopologicalSpace M] [T3Space M]
    [ConnectedSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M] (X : M → Fin 3 → ℝ)
    (embed : IsEmbedding X) (sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (imm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X x))
    (top : HasSinglePuncturedSurfaceTopology M)
    (nonplane : ∀ (T : ℂ →L[ℝ] (Fin 3 → ℝ)), Function.Injective T → ∀ o, ¬range X ⊆ range (fun w => o+T w))
    (minimal : ∀ x, coordinateMeanCurvature (X ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)=0)
    (hs : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,SurfaceEuclideanSpace) 1 (coordinateToEuclidean ∘ X))
    (di : ∀ x, Function.Injective (mvfderiv 𝓘(ℝ,ℂ) (coordinateToEuclidean ∘ X) x))
    (complete : letI := euclideanImmersionEMetricSpace (coordinateToEuclidean ∘ X) hs di
      CompleteSpace M) :
    Nonempty (PublishedConformalPoleModel X) ∧
    ∃ S : ChartedSpace ℂ M, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω M ∧ (∀ e∈atlas ℂ M, InducedIsothermalChart X e) ∧
      ∃ A : GeometricExteriorInSomeFrame X, A.exterior.correction 0=0 := by
  have transfer {e : OpenPartialHomeomorph M ℂ} (he : InducedIsothermalChart X e) :
      HarmonicImmersionChart X e := real_minimal_isothermal_chart_harmonic sm imm minimal he
  obtain ⟨S,man,charts,L,b,orth,⟨D⟩,β,bnz,asymptote⟩ :=
    bbc M X embed sm top nonplane minimal hs di complete
  let _ := S
  let _ := man
  have cy : Continuous (fun x => b+L (X x)) := continuous_const.add (L.toContinuousLinearEquiv.continuous.comp embed.continuous)
  obtain ⟨G,_,zero⟩ := D.normalized cy top.connected_tails
  let A : GeometricExteriorInSomeFrame X := ⟨L,orth,b,G,β,bnz,asymptote⟩
  exact ⟨exterior_frame_constructs_compact_pole_model embed.continuous (fun d hd => transfer (charts d hd)) top.connected_tails A,
    S,man,charts,A,zero⟩

theorem classical_finite_topology_gives_published_one_handle_model (bbc : PublishedFiniteOneEndDifferentialGeometry) :
    PublishedOneHandleEndTheorem := by
  intro s _ _ _
  let _ : T3Space s.carrier := s.closedEmbedding.isEmbedding.t3Space
  let _ : PathConnectedSpace (PuncturedPeriodTorus s.modelTorus) := punctured_torus_is_path_connected _
  let _ : ConnectedSpace s.carrier := s.topologicalType.symm.surjective.connectedSpace s.topologicalType.symm.continuous
  exact (finite_one_ended_surface_conformal_poles_and_normalized_end bbc s.position s.closedEmbedding.isEmbedding s.smooth
    s.immersion (original_one_puncture_surface_topology s) s.not_contained_in_parametric_plane s.minimal
    s.euclidean_smooth s.euclidean_immersion s.intrinsic_complete).1

/-- The original smooth handle already has infinite full Morse index
from the finite-topology end theorem alone. The analytic uniformization
of a compact genus-one surface plays no role in this implication. -/
theorem original_one_handle_index_from_general_end_theorem (bbc : PublishedFiniteOneEndDifferentialGeometry)
    (s : OriginalSmoothHelicoid) : ∃ S : ChartedSpace ℂ s.carrier, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω s.carrier ∧ (∀ e∈atlas ℂ s.carrier, InducedIsothermalChart s.position e) ∧
      HasInfiniteCompactSurfaceMorseIndex s.position := by
  have transfer {e : OpenPartialHomeomorph s.carrier ℂ} (he : InducedIsothermalChart s.position e) :
      HarmonicImmersionChart s.position e := real_minimal_isothermal_chart_harmonic s.smooth s.immersion s.minimal he
  obtain ⟨S,man,charts,⟨A⟩⟩ := published_finite_one_end_implies_original_exterior bbc s s.not_simply_connected
  let _ := S
  let _ := man
  exact ⟨S,man,charts,exterior_frame_implies_infinite_morse_index s.topologicalType s.position
    s.closedEmbedding.continuous (fun d hd => transfer (charts d hd)) A⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.finite_one_ended_surface_conformal_poles_and_normalized_end
#print axioms TwoAxisHelicoid.original_one_handle_index_from_general_end_theorem
