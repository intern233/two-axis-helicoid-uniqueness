import TwoAxisHelicoid.ChartGaussianShapeIdentity
import TwoAxisHelicoid.PhysicalFrameNormalDerivative
import TwoAxisHelicoid.PositionalCurvatureClassification

namespace TwoAxisHelicoid
open Complex Filter Set Topology
open scoped Topology ContDiff Manifold

/-- The Gaussian-curvature assertion of Meeks–Pérez, Corollary 1.2,
restricted to the complete, boundaryless, embedded finite-topology
surfaces used in TwoAxisHelicoid. The value is evaluated on the original position
map and its preferred smooth chart. -/
def FiniteTopologyGaussianCurvatureBound : Prop :=
  ∀ s : OriginalSmoothHelicoid, ∃ C : ℝ, 0≤C ∧ ∀ q : s.carrier,
    |chartGaussianCurvature (s.position ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q)|≤C

/-- The scalar curvature bound on the original surface implies the
physical shape bound needed for the thin-tube and single-layer graph
argument. The factor in the normalized frame is sqrt(C)/|pitch|. -/
theorem original_physical_shape_bound_of_gaussian (s : OriginalSmoothHelicoid)
    {C : ℝ} (hC : 0≤C) (bound : ∀ q : s.carrier,
      |chartGaussianCurvature (s.position ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q)|≤C) :
    HasBoundedPhysicalEndCurvature s := by
  refine ⟨∅,Real.sqrt C/|s.axes.pitch|,isCompact_empty,div_nonneg (Real.sqrt_nonneg _) (abs_nonneg _),?_⟩
  intro q _ v
  let e := chartAt ℂ q
  let Y := s.position ∘ e.symm
  let R := centeredHelicoidNormalization s.axes.pitch_ne
  have reg := smooth_surface_regular_manifold_chart s.smooth s.immersion q
  have hz : e q∈e.target := e.map_source (mem_chart_source ℂ q)
  obtain ⟨n,t⟩ := physical_frame_normal_derivative_lengths s.axes.pitch_ne reg hz v
  have b := minimal_gaussian_bound_implies_shape_bound reg hz (s.minimal q) hC (bound q) v
  change ‖fderiv ℝ (euclideanUnitChartNormal (R ∘ Y)) (e q) v‖≤
    Real.sqrt C/|s.axes.pitch| *‖coordinateToEuclidean (fderiv ℝ (R ∘ Y) (e q) v)‖
  rw [n,t,← mul_assoc,div_mul_cancel₀ _ (abs_ne_zero.mpr s.axes.pitch_ne)]
  exact b

/-- Weak one-sided positional asymptotics suffice for the unique spatial
class and embeddedness of the certified model, with the published scalar
curvature estimate, classical uniformization and embedded existence as
explicit premises. -/
theorem positional_unique_class_of_published_gaussian_bound
    (mp : FiniteTopologyGaussianCurvatureBound) (uni : SimplyConnectedNoncompactUniformization.{0})
    (whw : Nonempty OriginalPositionallyAsymptoticHelicoid) :
    (∃! c : Quotient (spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))),
      ∃ s : OriginalPositionallyAsymptoticHelicoid, Quotient.mk (spatialSimilaritySetoid _) s.image=c) ∧
      IsClosedEmbedding certifiedTorusImmersion := by
  apply positional_unique_class_of_bounded_curvature _ uni whw
  intro s
  obtain ⟨C,hC,bound⟩ := mp s.toOriginalSmoothHelicoid
  exact original_physical_shape_bound_of_gaussian s.toOriginalSmoothHelicoid hC bound

theorem positional_manuscript_calibration (s : OriginalPositionallyAsymptoticHelicoid)
    (mp : FiniteTopologyGaussianCurvatureBound) (uni : SimplyConnectedNoncompactUniformization.{0}) :
    Nonempty (PublishedConformalPoleModel s.position) ∧ HasCertifiedPointedNormalization s.toOriginalSmoothHelicoid ∧
      HasOriginalPointedGaussDivisor s.toOriginalSmoothHelicoid := by
  obtain ⟨C,hC,bound⟩ := mp s.toOriginalSmoothHelicoid
  exact positional_curvature_pointed_normalization s
    (original_physical_shape_bound_of_gaussian s.toOriginalSmoothHelicoid hC bound) uni

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_physical_shape_bound_of_gaussian
#print axioms TwoAxisHelicoid.positional_unique_class_of_published_gaussian_bound
#print axioms TwoAxisHelicoid.positional_manuscript_calibration
