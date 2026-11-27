import TwoAxisHelicoid.MaximalHarmonicImmersionChart
import TwoAxisHelicoid.OriginalExteriorTorusReduction

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology OnePoint Manifold ContDiff

universe u

/-- The local content of Bernstein–Breiner Theorem 1.1, in the ambient
frame selected by that theorem. The genuine punctured end chart and the
two orders concern the actual coordinate coefficients of the immersion. -/
structure GeometricDoublePoleEnd {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (X : M → Fin 3 → ℝ) where
  endChart : PuncturedComplexEnd M
  holomorphic : endChart.coord ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M
  height : MeromorphicAt (fun z => immersionComplexCoefficient (X ∘ endChart.coord.symm) z 2) 0
  heightOrder : meromorphicOrderAt (fun z => immersionComplexCoefficient (X ∘ endChart.coord.symm) z 2) 0 = -2
  gauss : MeromorphicAt (immersionGaussLogDerivative (X ∘ endChart.coord.symm)) 0
  gaussOrder : meromorphicOrderAt (immersionGaussLogDerivative (X ∘ endChart.coord.symm)) 0 = -2

/-- The original conformal puncture and pole statements suffice without a
normalized height primitive, exponential correction or an exterior radius
in the height coordinate. -/
theorem original_pole_end_marked_torus_reduction {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (uniform : CompactGenusOneUniformization.{u} L₀)
    (X : M → Fin 3 → ℝ) (hX : IsClosedEmbedding X) (hchart : ∀ d ∈ atlas ℂ M, HarmonicImmersionChart X d)
    (A : GeometricDoublePoleEnd X) :
    ∃ (L : PeriodPair) (f : M ≃ₜ PuncturedPeriodTorus L) (Y : PeriodTorus L → Fin 3 → ℝ),
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f.symm ∧
      (∀ x, Y (f x).1 = X x) ∧ IsClosedEmbedding (fun q : PuncturedPeriodTorus L => Y q.1) ∧
      range (fun q : PuncturedPeriodTorus L => Y q.1) = range X ∧
      (∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => Y (periodTorusProjection L w) j) z) ∧
        ConformalCoordinateDerivatives (Y ∘ periodTorusProjection L) z ∧
        Function.Injective (fderiv ℝ (Y ∘ periodTorusProjection L) z)) ∧
      MeromorphicAt (fun z => immersionComplexCoefficient (Y ∘ periodTorusProjection L) z 2) 0 ∧
      meromorphicOrderAt (fun z => immersionComplexCoefficient (Y ∘ periodTorusProjection L) z 2) 0 = -2 ∧
      MeromorphicAt (immersionGaussLogDerivative (Y ∘ periodTorusProjection L)) 0 ∧
      meromorphicOrderAt (immersionGaussLogDerivative (Y ∘ periodTorusProjection L)) 0 = -2 := by
  let E := A.endChart
  have hlc : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ℂ M
  let _ := compactifiedEndAtlas E
  have hman := compactifiedEndAtlas_isManifold E A.holomorphic
  have hcm : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) := hman
  have ht : OnePoint M ≃ₜ PeriodTorus L₀ := top.onePointCongr.trans (punctureCompactification (0:PeriodTorus L₀))
  obtain ⟨L,H,h0,hH,hi,hf,hir⟩ := compactified_uniformization_restricts E (uniform (OnePoint M) ⟨ht⟩)
  let f := markedPuncturedUniformization H h0
  let a : Fin 3 → ℝ := 0
  let Z := fun q : OnePoint M => q.elim a X
  let Y := Z ∘ H.symm
  have hfin (x : M) : Y (f x).1 = X x := by
    change (H.symm (H (x:OnePoint M))).elim a X = X x
    rw [H.symm_apply_apply]
    rfl
  obtain ⟨hclosed,him⟩ := marked_immersion_closedEmbedding_range H h0 X hX a
  have hhi := marked_harmonic_immersion_coordinates E X a hchart hman H h0 hH hi
  let V := X ∘ E.coord.symm
  let W := Z ∘ E.filledChart.symm
  have hV := harmonic_immersion_chart_maximal hchart A.holomorphic
  have hV' : ∀ᶠ w in 𝓝[≠] (0:ℂ), (∀ j, HarmonicAt (fun v => V v j) w) ∧ ConformalCoordinateDerivatives V w := by
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:ℂ) E.radius_pos),self_mem_nhdsWithin] with w hw hn
    have hh := hV w (E.mem_target_of_ball_ne hw hn)
    exact ⟨hh.1,hh.2.1⟩
  have hr := height_pole_implies_regular_gauss_germ hV' A.height (by rw [A.heightOrder]; decide)
  have he : W =ᶠ[𝓝[≠] (0:ℂ)] V := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    change w ≠ 0 at hw
    change (E.filledInverse w).elim a X = _
    simp [PuncturedComplexEnd.filledInverse,hw,V]
  obtain ⟨hcoeff,hlog⟩ := spatial_equal_germ_end_coefficients he
  have hheight := hcoeff.fun_comp (fun A => A 2)
  have hhp := A.height.congr hheight.symm
  have hho := (meromorphicOrderAt_congr hheight).trans A.heightOrder
  have hgp := A.gauss.congr hlog.symm
  have hgo := (meromorphicOrderAt_congr hlog).trans A.gaussOrder
  have hrr : ∀ᶠ w in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ W w ∧ DifferentiableAt ℂ (immersionGaussMap W) w := by
    filter_upwards [hr,punctured_germ_eventually_local he,punctured_germ_eventually_local (hcoeff.fun_comp nullGauss)] with w hw he' hg'
    exact ⟨hw.1.congr_of_eventuallyEq he',hw.2.congr_of_eventuallyEq hg'⟩
  have hχ : E.filledChart ∈ atlas ℂ (OnePoint M) := Or.inr rfl
  obtain ⟨h₁,h₂,h₃,h₄⟩ := uniformized_torus_actual_end_orders H OnePoint.infty h0 hH hi E.filledChart
    (IsManifold.subset_maximalAtlas hχ) OnePoint.infty_notMem_image_coe rfl Z hrr hhp hgp
  exact ⟨L,f,Y,hf,hir,hfin,hclosed,him,hhi,h₁,h₂.trans hho,h₃,h₄.trans hgo⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_pole_end_marked_torus_reduction
