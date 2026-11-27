import TwoAxisHelicoid.GeometricHelicoidHypotheses
import TwoAxisHelicoid.HarmonicMarkedTorusCompleteness
import TwoAxisHelicoid.HarmonicTangentLaplacian
import TwoAxisHelicoid.MinimalChartComplexData

namespace TwoAxisHelicoid
open Complex Set Filter Topology Matrix InnerProductSpace Laplacian
open scoped Topology ContDiff Manifold

/-- The chosen punctured-torus chart and the plane cover give the same local
parametrization, including all of its derivatives. -/
theorem marked_position_chart_germ (L : PeriodPair) (F : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (q : PuncturedPeriodTorus L) :
    F ∘ (chartAt ℂ q).symm =ᶠ[𝓝 (chartAt ℂ q q)] puncturedTorusPullback L F := by
  have hc := TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq
    (H := ℂ) (puncturedPeriodTorusOpen L) (x := q)
  filter_upwards [hc,L.isClosed_lattice.isOpen_compl.mem_nhds
    (puncturedPeriodTorus_chart_not_lattice L q)] with w hw hn
  change w ∉ L.lattice at hn
  have hp : ((chartAt ℂ q).symm w).1 = periodTorusProjection L w := by
    rw [← periodTorus_chart_symm_eq_projection L q.1]
    exact hw.symm
  change F ((chartAt ℂ q).symm w) = puncturedTorusPullback L F w
  rw [show puncturedTorusPullback L F w = F (puncturedPlaneProjection L ⟨w,hn⟩) by
    simp [puncturedTorusPullback,hn]]
  exact congrArg F (Subtype.ext hp)

/-- Vanishing of the Euclidean mean curvature in the actual quotient atlas.
All three ambient coordinates are harmonic on the regular plane cover. -/
theorem marked_harmonic_chart_mean_curvature_zero (L : PeriodPair) (F : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hh : ∀ z ∉ L.lattice, ∀ j, HarmonicAt (fun w => puncturedTorusPullback L F w j) z)
    (hc : ∀ z ∉ L.lattice, ConformalCoordinateDerivatives (puncturedTorusPullback L F) z)
    (q : PuncturedPeriodTorus L) :
    coordinateMeanCurvature (F ∘ (chartAt ℂ q).symm) (chartAt ℂ q q) = 0 := by
  let z := chartAt ℂ q q
  let P := puncturedTorusPullback L F
  have hz : z ∉ L.lattice := puncturedPeriodTorus_chart_not_lattice L q
  have eq := marked_position_chart_germ L F q
  have ha : AnalyticAt ℝ P z := analyticAt_pi_iff.mpr fun j => HarmonicAt.analyticAt (hh z hz j)
  have harm : HarmonicAt P z := by
    refine ⟨ha.contDiffAt,?_⟩
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact harmonic_coordinate_laplacian_zero (hh w hw)
  have ⟨hs,ho⟩ := (conformalCoordinateDerivatives_iff_dot ha.differentiableAt).mp (hc z hz)
  apply conformal_harmonic_coordinate_mean_curvature_zero ((harmonicAt_congr_nhds eq).mpr harm)
  · rfl
  · rw [eq.fderiv_eq]
    exact hs.symm
  · rw [eq.fderiv_eq]
    exact ho

/-- Forget the marking of an embedded conformal harmonic torus to obtain an
original real smooth minimal surface with its actual marked spatial lines. -/
noncomputable def markedMinimalGeometricSurface (L : PeriodPair) (F : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (he : IsClosedEmbedding F) (axes : OriginalHelicoidAxes (range F))
    (hh : ∀ z ∉ L.lattice, ∀ j, HarmonicAt (fun w => puncturedTorusPullback L F w j) z)
    (hc : ∀ z ∉ L.lattice, ConformalCoordinateDerivatives (puncturedTorusPullback L F) z)
    (hi : ∀ z ∉ L.lattice, Function.Injective (fderiv ℝ (puncturedTorusPullback L F) z)) :
    OriginalSmoothHelicoid where
  carrier := PuncturedPeriodTorus L
  modelTorus := L
  topologicalType := Homeomorph.refl _
  position := F
  closedEmbedding := he
  smooth := (harmonic_marked_torus_contMDiff L F hh).of_le (by simp)
  immersion q := by
    rw [(harmonic_marked_torus_hasMFDerivAt L F hh q).mfderiv]
    exact hi _ (puncturedPeriodTorus_chart_not_lattice L q)
  minimal := marked_harmonic_chart_mean_curvature_zero L F hh hc
  axes := axes

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.markedMinimalGeometricSurface
