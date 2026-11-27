import TwoAxisHelicoid.GeneralBBCExteriorGerm
import TwoAxisHelicoid.ProperImmersedPlaneRigidity
import TwoAxisHelicoid.PublishedFiniteTopologyCurvature
import TwoAxisHelicoid.OriginalPositionalHelicoid

namespace TwoAxisHelicoid
open Complex Matrix Set Topology
open scoped Topology ContDiff Manifold

/-- Finite topology with one end, without a genus restriction. -/
def HasSinglePuncturedSurfaceTopology (M : Type) [TopologicalSpace M] : Prop :=
  ∃ (K : Type) (t : TopologicalSpace K), let _ := t
    T2Space K ∧ CompactSpace K ∧ ConnectedSpace K ∧ Nonempty (ChartedSpace ℂ K) ∧
      ∃ p : K, Nonempty (M ≃ₜ {q : K // q≠p})

/-- The finite-topology differential end theorem of Bernstein--Breiner
(Theorem 1.1 and Corollaries 1.2 and 1.3). The immersion is complete in
its induced length metric. The geometric statement is made in a rigid
frame of the end theorem; it imposes no axes, genus-one marking, global
Weierstrass parameters or period equations. -/
def PublishedFiniteOneEndDifferentialGeometry : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T3Space M] [ConnectedSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℝ,ℂ) ∞ M] (X : M → Fin 3 → ℝ), IsEmbedding X →
    ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X → HasSinglePuncturedSurfaceTopology M →
    (∀ (T : ℂ →L[ℝ] (Fin 3 → ℝ)), Function.Injective T → ∀ o, ¬range X ⊆ range (fun w => o+T w)) →
    (∀ x, coordinateMeanCurvature (X ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)=0) →
    ∀ (hs : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,SurfaceEuclideanSpace) 1 (coordinateToEuclidean ∘ X))
      (di : ∀ x, Function.Injective (mvfderiv 𝓘(ℝ,ℂ) (coordinateToEuclidean ∘ X) x)),
      (letI := euclideanImmersionEMetricSpace (coordinateToEuclidean ∘ X) hs di
       CompleteSpace M) →
      ∃ S : ChartedSpace ℂ M, let _ := S
        IsManifold 𝓘(ℂ,ℂ) ω M ∧ (∀ e∈atlas ℂ M, InducedIsothermalChart X e) ∧
        ∃ (L : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) (b : Fin 3 → ℝ),
          (∀ v w, L v ⬝ᵥ L w=v ⬝ᵥ w) ∧ Nonempty (FiniteTopologyExteriorDifferential (fun x => b+L (X x))) ∧
          ∃ β : ℝ, β≠0 ∧ ApproachesSetAtInfinity (range (axisRuledHelicoid I β 0)) (range (fun x => b+L (X x)))

theorem original_one_puncture_surface_topology (s : OriginalSmoothHelicoid) :
    HasSinglePuncturedSurfaceTopology s.carrier := by
  let L := s.modelTorus
  let _ : T1Space (PeriodTorus L) := QuotientAddGroup.t1Space_iff.mpr L.isClosed_lattice
  have connected : ConnectedSpace (PeriodTorus L) := (Quotient.mk_surjective :
    Function.Surjective (periodTorusProjection L)).connectedSpace QuotientAddGroup.continuous_mk
  exact ⟨PeriodTorus L,inferInstance,inferInstance,periodTorus_compactSpace L,connected,⟨inferInstance⟩,0,⟨s.topologicalType⟩⟩

/-- Verify every global hypothesis against the original smooth physical
surface, then integrate the differential in the exterior chart. -/
theorem published_finite_one_end_implies_original_exterior (bbc : PublishedFiniteOneEndDifferentialGeometry) :
    OneHandleGeometricExteriorPrinciple := by
  intro s _
  let _ : T3Space s.carrier := s.closedEmbedding.isEmbedding.t3Space
  let _ : PathConnectedSpace (PuncturedPeriodTorus s.modelTorus) := punctured_torus_is_path_connected _
  let _ : ConnectedSpace s.carrier := s.topologicalType.symm.surjective.connectedSpace s.topologicalType.symm.continuous
  obtain ⟨S,man,charts,L,b,orth,⟨G⟩,β,non,approaches⟩ :=
    bbc s.carrier s.position s.closedEmbedding.isEmbedding s.smooth (original_one_puncture_surface_topology s)
      s.not_contained_in_parametric_plane s.minimal s.euclidean_smooth s.euclidean_immersion s.intrinsic_complete
  let _ := S
  exact ⟨S,man,charts,⟨⟨L,orth,b,G.toExterior,β,non,approaches⟩⟩⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.published_finite_one_end_implies_original_exterior
