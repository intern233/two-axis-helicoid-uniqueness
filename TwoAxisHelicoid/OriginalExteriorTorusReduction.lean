import TwoAxisHelicoid.MarkedHarmonicImmersion
import TwoAxisHelicoid.UniformizedEndCoordinate
import TwoAxisHelicoid.HarmonicExteriorCoordinates
import TwoAxisHelicoid.ExteriorHeightCompactCore
import TwoAxisHelicoid.ExteriorGaussRegularity

namespace TwoAxisHelicoid
open Bornology Complex Set Filter Topology InnerProductSpace
open scoped Topology OnePoint ContDiff Manifold

universe u

/-- The classical genus-one uniformization statement specialized to a
specified compact topological torus. It quantifies over its given complex
structure; the resulting generators and analytic marking are conclusions. -/
def CompactGenusOneUniformization (L₀ : PeriodPair) : Prop :=
  ∀ (N : Type u) [TopologicalSpace N] [CompactSpace N] [T2Space N] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ,ℂ) ω N], Nonempty (N ≃ₜ PeriodTorus L₀) → AdmitsPeriodTorusUniformization N

/-- The genuine conformal exterior height coordinate and Gauss formula
used from the geometric asymptotic theorem. The domain is an open
neighborhood with compact complement on the original surface. -/
structure GeometricExteriorCoordinate {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (X : M → Fin 3 → ℝ) where
  chart : OpenPartialHomeomorph M ℂ
  radius : ℝ
  positive : 0 < radius
  target : chart.target = {ζ : ℂ | radius < ‖ζ‖}
  core : IsCompact chart.sourceᶜ
  holomorphic : chart ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M
  heightOffset : ℝ
  height : ∀ x ∈ chart.source, X x 2 = heightOffset+(chart x).re
  pitch : ℝ
  pitch_ne : pitch ≠ 0
  correction : ℂ → ℂ
  analytic : AnalyticAt ℂ correction 0
  gauss : ∀ᶠ ζ in cobounded ℂ, immersionGaussMap (X ∘ chart.symm) ζ =
    Complex.exp (I*(pitch:ℂ)*ζ+correction ζ⁻¹)

/-- Starting with a genuine once-punctured topological torus, its actual
harmonic immersion, the geometric exterior coordinate, and classical
uniformization, construct the actual marked torus, its finite biholomorphism,
its regular harmonic lift and the two meromorphic double poles. -/
theorem original_surface_marked_torus_reduction {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (uniform : CompactGenusOneUniformization.{u} L₀)
    (X : M → Fin 3 → ℝ) (hX : IsClosedEmbedding X) (hchart : ∀ d ∈ atlas ℂ M, HarmonicImmersionChart X d)
    (A : GeometricExteriorCoordinate X) :
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
  let e := A.chart
  have htail : HasConnectedCompactTails M := homeomorphic_punctured_surface_connected_tails (0:PeriodTorus L₀) top
  have hheight : Continuous (fun x => X x 2) := (continuous_apply 2).comp hX.continuous
  have hnc : NoncompactSpace M := noncompact_of_exterior_height e A.target _ hheight A.heightOffset A.height
  have hlc : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ℂ M
  have hesc := true_exterior_height_coordinate_escapes htail e A.target A.core _ hheight A.heightOffset A.height
  let E := exteriorCoordinateComplexEnd e A.positive A.target A.core hesc
  let _ := compactifiedEndAtlas E
  have hman := (exteriorCoordinate_fills_complex_manifold e A.positive A.target A.core hesc A.holomorphic).1
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
  have hreg := exterior_immersion_eventually_differentiable X hchart A.holomorphic A.target
  have hh : ∀ᶠ ζ in cobounded ℂ, X (e.symm ζ) 2 = A.heightOffset+ζ.re := by
    filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop A.radius)] with ζ hz
    have hζ : ζ ∈ e.target := A.target ▸ hz
    rw [A.height _ (e.map_target hζ),e.right_inv hζ]
  obtain ⟨hhp,hho,hgp,hgo⟩ := compactified_exterior_surface_end_poles X e A.positive A.target A.core hesc
    A.heightOffset A.pitch A.pitch_ne A.correction A.analytic hreg hh A.gauss a
  have hrr := compactified_exterior_end_regular X e A.positive A.target A.core hesc
    A.pitch A.correction A.analytic hreg A.gauss a
  have hχ : E.filledChart ∈ atlas ℂ (OnePoint M) := Or.inr rfl
  obtain ⟨h₁,h₂,h₃,h₄⟩ := uniformized_torus_actual_end_orders H OnePoint.infty h0 hH hi E.filledChart
    (IsManifold.subset_maximalAtlas hχ) OnePoint.infty_notMem_image_coe rfl Z hrr hhp hgp
  exact ⟨L,f,Y,hf,hir,hfin,hclosed,him,hhi,h₁,h₂.trans hho,h₃,h₄.trans hgo⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_surface_marked_torus_reduction
