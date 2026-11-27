import TwoAxisHelicoid.ChartGaussianShapeIdentity
import TwoAxisHelicoid.OriginalHelicoidMetric
import TwoAxisHelicoid.OpenPuncturedCoreConnectivity

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold

/-- A boundaryless surface of finite topological type, expressed as a
compact connected topological surface minus a finite set of points. -/
def HasFinitePuncturedSurfaceTopology (M : Type) [TopologicalSpace M] : Prop :=
  ∃ (K : Type) (t : TopologicalSpace K), let _ := t
    T2Space K ∧ CompactSpace K ∧ ConnectedSpace K ∧ Nonempty (ChartedSpace ℂ K) ∧
      ∃ P : Set K, P.Finite ∧ Nonempty (M ≃ₜ ↥(Pᶜ : Set K))

/-- The curvature assertion of Meeks and Pérez, Corollary 1.2, for
complete, connected embedded minimal surfaces without boundary. The
metric in the completeness hypothesis is the actual pullback length
metric. The assertion involves no helicoid, straight lines or poles. -/
def PublishedFiniteTopologyGaussianCurvature : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T3Space M] [ConnectedSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℝ,ℂ) ∞ M] (X : M → Fin 3 → ℝ), IsEmbedding X →
    ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X → HasFinitePuncturedSurfaceTopology M →
    (∀ x, coordinateMeanCurvature (X ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)=0) →
    ∀ (hs : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,SurfaceEuclideanSpace) 1 (coordinateToEuclidean ∘ X))
      (di : ∀ x, Function.Injective (mvfderiv 𝓘(ℝ,ℂ) (coordinateToEuclidean ∘ X) x)),
      (letI := euclideanImmersionEMetricSpace (coordinateToEuclidean ∘ X) hs di
       CompleteSpace M) →
      ∃ C : ℝ, 0≤C ∧ ∀ q : M, |chartGaussianCurvature (X ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q)|≤C

theorem original_compact_surface_minus_one_point (s : OriginalSmoothHelicoid) : HasFinitePuncturedSurfaceTopology s.carrier := by
  let L := s.modelTorus
  let _ : T1Space (PeriodTorus L) := QuotientAddGroup.t1Space_iff.mpr L.isClosed_lattice
  have con : ConnectedSpace (PeriodTorus L) := (Quotient.mk_surjective : Function.Surjective (periodTorusProjection L)).connectedSpace
    QuotientAddGroup.continuous_mk
  refine ⟨PeriodTorus L,inferInstance,inferInstance,periodTorus_compactSpace L,con,⟨inferInstance⟩,
    {(0:PeriodTorus L)},finite_singleton _,⟨s.topologicalType⟩⟩

/-- All geometric and topological hypotheses of the published estimate
hold on the original representative with its original real charts.
In particular completeness follows from its proper spatial embedding. -/
theorem original_gaussian_bound_of_finite_topology_publication (mp : PublishedFiniteTopologyGaussianCurvature)
    (s : OriginalSmoothHelicoid) :
    ∃ C : ℝ, 0≤C ∧ ∀ q : s.carrier,
      |chartGaussianCurvature (s.position ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q)|≤C := by
  let _ : T3Space s.carrier := s.closedEmbedding.isEmbedding.t3Space
  let _ : PathConnectedSpace (PuncturedPeriodTorus s.modelTorus) := punctured_torus_is_path_connected _
  let _ : ConnectedSpace s.carrier := s.topologicalType.symm.surjective.connectedSpace s.topologicalType.symm.continuous
  exact mp s.carrier s.position s.closedEmbedding.isEmbedding s.smooth (original_compact_surface_minus_one_point s)
    s.minimal s.euclidean_smooth s.euclidean_immersion s.intrinsic_complete

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_compact_surface_minus_one_point
#print axioms TwoAxisHelicoid.original_gaussian_bound_of_finite_topology_publication
