import TwoAxisHelicoid.PhysicalRegionJacobiFlux

namespace TwoAxisHelicoid
open Complex Set MeasureTheory Topology Filter Function InnerProductSpace Laplacian Matrix
open scoped Topology Manifold ContDiff

/-- A classical scalar Jacobi field in the actual isothermal coordinates
of the specified spatial immersion. -/
def IsSurfaceJacobiField {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (X : M → Fin 3 → ℝ) (u : M → ℝ) : Prop :=
  ∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M, ∀ z∈e.target,
    ContDiffAt ℝ 2 (u ∘ e.symm) z ∧ conformalSurfaceJacobi (X ∘ e.symm) (u ∘ e.symm) z=0

/-- The intrinsic energy of u on the region. Its coordinate formula
contains the inverse metric in the gradient term, the squared shape
operator, and the induced surface area factor. -/
noncomputable def CurveRegionPartition.jacobiEnergy {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {Ω : Set M} (P : CurveRegionPartition Ω) (X : M → Fin 3 → ℝ) (u : M → ℝ) : ℝ :=
  P.areaIntegral (fun i z =>
    let Y := X ∘ (P.chart i).symm
    let U := u ∘ (P.chart i).symm
    let g := planePartial 1 Y z ⬝ᵥ planePartial 1 Y z
    ((planePartial 1 U z^2+planePartial I U z^2)/g-jacobiPotentialDensity Y z/g*(U z)^2)*g)

/-- Both identities of Appendix D.4 on any relatively compact smooth
region. The first is the vanishing Wronskian boundary integral. In the
second the physical boundary flux equals the intrinsic Jacobi energy.
A finite localization exists, and the equations hold for every such
localization of the same region. -/
theorem smooth_region_jacobi_green_identities {M : Type*} [TopologicalSpace M] [T2Space M]
    [SigmaCompactSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {Ω : Set M} (opened : IsOpen Ω) (compact : IsCompact (closure Ω)) (boundary : HasSmoothCurveBoundary Ω)
    (X : M → Fin 3 → ℝ) (hX : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (u v : M → ℝ) (uJacobi : IsSurfaceJacobiField X u) (vJacobi : IsSurfaceJacobiField X v) :
    Nonempty (CurveRegionPartition Ω) ∧ ∀ P : CurveRegionPartition Ω,
      P.jacobiBoundaryFlux u v X-P.jacobiBoundaryFlux v u X=0 ∧ P.jacobiEnergy X u=P.jacobiBoundaryFlux u u X := by
  classical
  refine ⟨exists_curve_region_partition opened compact boundary,?_⟩
  intro P
  have u2 (i : P.indices) z (hz : z∈(P.chart i).target) := (uJacobi _ (P.member i) z hz).1
  have v2 (i : P.indices) z (hz : z∈(P.chart i).target) := (vJacobi _ (P.member i) z hz).1
  have su (i : P.indices) z (hz : z∈(P.chart i).target) := (uJacobi _ (P.member i) z hz).2
  have sv (i : P.indices) z (hz : z∈(P.chart i).target) := (vJacobi _ (P.member i) z hz).2
  have uv := surface_region_jacobi_green opened P X u v hX (fun i z hz => (u2 i z hz).of_le (by norm_num)) v2 sv
  have vu := surface_region_jacobi_green opened P X v u hX (fun i z hz => (v2 i z hz).of_le (by norm_num)) u2 su
  have uu := surface_region_jacobi_green opened P X u u hX (fun i z hz => (u2 i z hz).of_le (by norm_num)) u2 su
  constructor
  · rw [sub_eq_zero,← uv,← vu]
    apply Finset.sum_congr rfl
    intro i _
    apply setIntegral_congr_fun (isOpen_curveChartRegion (P.chart i) opened).measurableSet
    intro z _
    dsimp only
    ring
  · rw [← uu]
    apply Finset.sum_congr rfl
    intro i _
    apply setIntegral_congr_fun (isOpen_curveChartRegion (P.chart i) opened).measurableSet
    intro z hz
    let Y := X ∘ (P.chart i).symm
    have reg := harmonic_immersion_chart_maximal hX (P.member i) z hz.1
    have diff : AnalyticAt ℝ Y z := analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (reg.1 j))
    have pos := (harmonicChartNormal_data diff reg.2.1 reg.2.2).2.1.ne'
    dsimp only [CurveRegionPartition.jacobiEnergy,CurveRegionPartition.areaIntegral]
    dsimp only [Y] at pos
    field_simp [pos]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_region_jacobi_green_identities

