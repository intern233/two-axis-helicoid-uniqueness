import TwoAxisHelicoid.CompactCurveSinglePunctureResidue
import TwoAxisHelicoid.CompactifiedHarmonicCharts
import TwoAxisHelicoid.GeometricGraphCompactification
import TwoAxisHelicoid.OriginalPoleEndTorusReduction

namespace TwoAxisHelicoid
open Complex Set Filter Metric Topology
open scoped Topology ContDiff Manifold
universe u

/-- All three conormal fluxes vanish on sufficiently small peripheral
circles of a one-ended compactified harmonic immersion, in every genus. -/
theorem physical_harmonic_end_zero_peripheral_flux {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {X : M → Fin 3 → ℝ} (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (E : PuncturedComplexEnd M) (hol : E.coord∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    (j : Fin 3) : ∃ R : ℝ, 0<R ∧ ∀ r∈Ioo (0:ℝ) R,
      (∮ z in C(0,r), immersionComplexCoefficient (X ∘ E.coord.symm) z j)=0 := by
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ℂ M
  let _ := compactifiedEndAtlas E
  let _ := compactifiedEndAtlas_isManifold E hol
  let Z := fun p : OnePoint M => p.elim 0 X
  let Y := X ∘ E.coord.symm
  let a := fun (e : OpenPartialHomeomorph (OnePoint M) ℂ) z => immersionComplexCoefficient (Z ∘ e.symm) z j
  have germ : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ (fun v => immersionComplexCoefficient Y v j) z := by
    have h := harmonic_immersion_chart_maximal charts hol
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) E.radius_pos)] with z nz near
    exact (scalarComplexCoefficient_analyticAt ((h z (E.mem_target_of_ball_ne near nz)).1 j)).differentiableAt
  obtain ⟨c,res⟩ := exists_puncture_residue germ
  obtain ⟨coeffHol,overlap⟩ := filled_chart_physical_coefficient_law charts E hol 0 j
  have atlas : E.filledChart∈atlas ℂ (OnePoint M) := Or.inr rfl
  have eq : (Z ∘ E.filledChart.symm) =ᶠ[𝓝[≠] (0:ℂ)] Y := by
    filter_upwards [self_mem_nhdsWithin] with z nz
    change (E.filledInverse z).elim 0 X=_
    simp [PuncturedComplexEnd.filledInverse,show z≠0 from nz,Y]
  have same := (spatial_equal_germ_end_coefficients eq).1.fun_comp (fun v => v j)
  have res' : HasPunctureResidue (a E.filledChart) c := by
    obtain ⟨F,d⟩ := res
    refine ⟨F,?_⟩
    filter_upwards [d,same] with z hz he
    exact (show a E.filledChart z=immersionComplexCoefficient Y z j from he).symm ▸ hz
  have zero := compact_curve_single_puncture_residue_zero (P:=OnePoint.infty) a coeffHol overlap
    (IsManifold.subset_maximalAtlas atlas) OnePoint.infty_notMem_image_coe rfl res'
  obtain ⟨R,Rp,all⟩ := res.small_circle_integrals germ
  exact ⟨R,Rp,fun r hr => (all r hr).trans (by simp [zero])⟩

/-- The two meromorphic differentials are measured in the original
conformal structure of the given embedded harmonic graph. -/
theorem physical_harmonic_graph_double_pole_end {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [NoncompactSpace M]
    (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (graph : HasHelicoidC1End (coordinateToTube ∘ X)) :
    ∃ A : GeometricDoublePoleEnd X, let _ := compactifiedEndAtlas A.endChart
        IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) ∧
          ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (OnePoint.some : M → OnePoint M) := by
  obtain ⟨E,hol,compactified,orders⟩ := harmonic_graph_compactification X closed charts graph
  have flux (j : Fin 3) (ε : ℝ) (ep : 0<ε) : ∃ r∈Ioo (0:ℝ) ε,
      (∮ z in C(0,r), immersionComplexCoefficient (X ∘ E.coord.symm) z j).im=0 := by
    obtain ⟨R,Rp,zero⟩ := physical_harmonic_end_zero_peripheral_flux charts E hol j
    let r := min R ε/2
    have rp : 0<r := half_pos (lt_min Rp ep)
    have left : r<R := (half_lt_self (lt_min Rp ep)).trans_le (min_le_left _ _)
    have right : r<ε := (half_lt_self (lt_min Rp ep)).trans_le (min_le_right _ _)
    exact ⟨r,⟨rp,right⟩,congrArg Complex.im (zero r ⟨rp,left⟩)⟩
  obtain ⟨⟨h,ho⟩,g,go⟩ := orders flux
  exact ⟨⟨E,hol,h,ho,g,go⟩,compactified⟩

/-- The compactification and the two double poles of Proposition 2.1
for an actual smooth oriented embedded minimal surface with a physical
C¹ helicoidal end. No genus, axis or flux assumption enters the theorem. -/
theorem oriented_minimal_graph_double_pole_compactification {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M] [NoncompactSpace M]
    (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (smooth : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (immersion : ∀ q, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X q))
    (orientation : PositiveSurfaceAtlas M)
    (minimal : ∀ q, coordinateMeanCurvature (X ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q)=0)
    (graph : HasHelicoidC1End (coordinateToTube ∘ X)) :
    ∃ S : ChartedSpace ℂ M, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω M ∧ (∀ d∈atlas ℂ M, HarmonicImmersionChart X d) ∧
      ∃ A : GeometricDoublePoleEnd X, let _ := compactifiedEndAtlas A.endChart
        IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) ∧
          ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (OnePoint.some : M → OnePoint M) := by
  obtain ⟨S,man,charts⟩ := oriented_minimal_induced_harmonic_atlas smooth immersion orientation minimal
  let _ := S
  let _ := man
  exact ⟨S,man,charts,physical_harmonic_graph_double_pole_end X closed charts graph⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.physical_harmonic_end_zero_peripheral_flux
#print axioms TwoAxisHelicoid.physical_harmonic_graph_double_pole_end
#print axioms TwoAxisHelicoid.oriented_minimal_graph_double_pole_compactification
