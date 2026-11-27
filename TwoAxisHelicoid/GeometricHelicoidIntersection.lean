import TwoAxisHelicoid.MarkedMinimalGeometricSurface
import TwoAxisHelicoid.OriginalSurfaceNonperiodicity
import TwoAxisHelicoid.OriginalHelicoidMetric
import TwoAxisHelicoid.HoffmanWhiteWindingReduction

namespace TwoAxisHelicoid
open Complex Matrix Set Filter Topology Manifold InnerProductSpace
open scoped Topology ContDiff Manifold

/-- The geometric intersection theorem in the coordinates of the two
perpendicular spatial axes. Its hypotheses concern the actual real surface,
its induced length metric, the two lines, the helicoidal end and the absence
of nontrivial screw periods. It imposes no condition on its complex marking. -/
def GeometricTwoAxisIntersectionTheorem : Prop :=
  ∀ (s : OriginalSmoothHelicoid) {α : ℝ} (hα : α ≠ 0) (b : ℝ),
    let A := axisSpatialNormalization hα ![0,0,b]
    let H := A ⁻¹' range (fun w : ℂ => standardHelicoid w.re w.im)
    (letI : T3Space s.carrier := s.closedEmbedding.isEmbedding.t3Space
     letI := euclideanImmersionEMetricSpace s.euclideanPosition s.euclidean_smooth s.euclidean_immersion
     CompleteSpace s.carrier) →
    (∀ (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)) {d : ℝ}, d ≠ 0 → (∀ p, R p 2 = p 2+d) →
      R '' range s.position ≠ range s.position) →
    (∀ r : ℝ, (![r,0,0] : Fin 3 → ℝ) ∈ range s.position) →
    (∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ) ∈ range s.position) →
    HasHelicoidC1End (coordinateToTube ∘ A ∘ s.position) →
    H = range (axisRuledHelicoid I α 0) →
    range s.position ∩ H = {P | (P 1 = 0 ∧ P 2 = 0) ∨ (P 0 = 0 ∧ P 1 = 0)}

/-- All geometric hypotheses for the published intersection theorem follow
from the marked input. In particular the real surface is smooth and minimal,
its induced metric is complete, and the handle excludes nonzero screw periods. -/
theorem rhombic_intersection_of_geometric_theorem (hw : GeometricTwoAxisIntersectionTheorem) :
    RhombicHelicoidIntersectionPrinciple := by
  intro t ht X hX α hα b F A H he hh hv hend hH
  let L := rhombicPeriodPair t ht
  have germ (z : ℂ) (hz : z ∉ L.lattice) : puncturedTorusPullback L F =ᶠ[𝓝 z] X := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    change w ∉ L.lattice at hw
    rw [show puncturedTorusPullback L F w = F (puncturedPlaneProjection L ⟨w,hw⟩) by
      simp [puncturedTorusPullback,hw]]
    exact harmonicTorusImmersion_projection hX hw
  let axes : OriginalHelicoidAxes (range F) :=
    { horizontalDirection := 1
      unit := by simp
      horizontalPoint := 0
      horizontal := fun r => by
        have eq : (0 : Fin 3 → ℝ)+r • ![(1 : ℂ).re,(1 : ℂ).im,0] = ![r,0,0] := by
          ext j
          fin_cases j <;> simp
        rw [eq]
        exact hh r
      vertical := hv
      pitch := α
      pitch_ne := hα }
  have hform (z : ℂ) (hz : z ∉ L.lattice) : ConformalCoordinateDerivatives (puncturedTorusPullback L F) z := by
    have hd (j : Fin 3) : fderiv ℝ (fun w => puncturedTorusPullback L F w j) z = fderiv ℝ (fun w => X w j) z := by
      have h : (fun w => puncturedTorusPullback L F w j) =ᶠ[𝓝 z] (fun w => X w j) :=
        (germ z hz).mono (fun _ ew => congrFun ew j)
      exact h.fderiv_eq
    simpa only [ConformalCoordinateDerivatives,hd] using hX.conformal z hz
  let s := markedMinimalGeometricSurface L F he axes
    (fun z hz j => (harmonicAt_congr_nhds ((germ z hz).mono (fun _ ew => congrFun ew j))).mpr (hX.harmonic z hz j))
    hform (fun z hz => by rw [(germ z hz).fderiv_eq]; exact hX.immersion z hz)
  exact hw s hα b s.intrinsic_complete (fun R _ hd h => s.no_nonzero_screw_step R hd h) hh hv hend hH

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rhombic_intersection_of_geometric_theorem
