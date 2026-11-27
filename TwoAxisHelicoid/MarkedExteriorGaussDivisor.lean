import TwoAxisHelicoid.OriginalExteriorTorusReduction
import TwoAxisHelicoid.UniformizedGaussEndResidue
import TwoAxisHelicoid.VerticalFluxTorusCrossing

namespace TwoAxisHelicoid
open Bornology Complex Set Filter Topology InnerProductSpace
open scoped Topology OnePoint ContDiff Manifold

universe u

/-- The actual Gauss exponential on the exterior gives its reciprocal-coordinate
expression on the filled surface. Values assigned at the added point are immaterial. -/
theorem filled_exterior_gauss_exponential {M : Type*} [TopologicalSpace M] [T2Space M]
    [WeaklyLocallyCompactSpace M] [NoncompactSpace M] [ChartedSpace ℂ M]
    (X : M → Fin 3 → ℝ) (A : GeometricExteriorCoordinate X)
    (he : Tendsto (fun x => ‖A.chart x‖) (cocompact M) atTop)
    (hr : ∀ᶠ ζ in cobounded ℂ, DifferentiableAt ℝ (X ∘ A.chart.symm) ζ)
    (a : Fin 3 → ℝ) :
    let E := exteriorCoordinateComplexEnd A.chart A.positive A.target A.core he
    let Z := fun w : ℂ => (E.filledChart.symm w).elim a X
    immersionGaussMap Z =ᶠ[𝓝[≠] (0:ℂ)] fun w => Complex.exp ((I*(A.pitch:ℂ))/w+A.correction w) := by
  let E := exteriorCoordinateComplexEnd A.chart A.positive A.target A.core he
  let Z := fun w : ℂ => (E.filledChart.symm w).elim a X
  let Y := (X ∘ A.chart.symm) ∘ fun w : ℂ => w⁻¹
  have e : Z =ᶠ[𝓝[≠] (0:ℂ)] Y := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    change w ≠ 0 at hw
    change (E.filledInverse w).elim a X = _
    rw [PuncturedComplexEnd.filledInverse,ite_eq_right_iff.mpr (fun h => (hw h).elim)]
    rfl
  filter_upwards [(spatial_equal_germ_end_coefficients e).1,tendsto_inv₀_nhdsNE_zero.eventually A.gauss,
    tendsto_inv₀_nhdsNE_zero.eventually hr,self_mem_nhdsWithin] with w hw hg hreg hn
  change w ≠ 0 at hn
  have d : immersionGaussMap Y w = immersionGaussMap (X ∘ A.chart.symm) w⁻¹ :=
    immersionGaussMap_comp_holomorphic hreg (hasDerivAt_inv hn) (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hn)))
  exact (congrArg nullGauss hw).trans (d.trans (by simpa only [div_eq_mul_inv,inv_inv] using hg))

/-- Analytic end data and all regularity statements refer to one specific
marked immersion, with the ordinary derivative of its Gauss map. -/
structure MarkedHelicoidalEndForms (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ) : Prop where
  regular : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
    ConformalCoordinateDerivatives (puncturedTorusPullback L X) z ∧ Function.Injective (fderiv ℝ (puncturedTorusPullback L X) z)
  height_order : meromorphicOrderAt (fun z => torusImmersionForms L X z 2) 0 = (-2:ℤ)
  gauss_expansion : ∃ (κ : ℂ) (R : ℂ → ℂ), κ ≠ 0 ∧ AnalyticAt ℂ R 0 ∧
    ∀ᶠ z in 𝓝[≠] (0:ℂ), logDeriv (nullGauss ∘ torusImmersionForms L X) z = κ/z^2+R z

/-- The end orders and the residue-free logarithmic expansion in any
specified pointed biholomorphic compact filling. This includes the
original marking when the conformal punctured torus is already given. -/
theorem exterior_forms_in_pointed_filling {M : Type*} [TopologicalSpace M] [T2Space M]
    [WeaklyLocallyCompactSpace M] [NoncompactSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    (X : M → Fin 3 → ℝ) (hchart : ∀ d ∈ atlas ℂ M, HarmonicImmersionChart X d)
    (A : GeometricExteriorCoordinate X) (hesc : Tendsto (fun x => ‖A.chart x‖) (cocompact M) atTop)
    {L : PeriodPair} (H : OnePoint M ≃ₜ PeriodTorus L) (h0 : H OnePoint.infty=0) :
    let E := exteriorCoordinateComplexEnd A.chart A.positive A.target A.core hesc
    let _ := compactifiedEndAtlas E
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H → ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm →
      MarkedHelicoidalEndForms L (fun q => (H.symm q.1).elim (0:Fin 3 → ℝ) X) := by
  let e := A.chart
  let E := exteriorCoordinateComplexEnd e A.positive A.target A.core hesc
  let _ := compactifiedEndAtlas E
  have hm : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) :=
    (exteriorCoordinate_fills_complex_manifold e A.positive A.target A.core hesc A.holomorphic).1
  let Z := fun q : OnePoint M => q.elim (0:Fin 3 → ℝ) X
  let full := Z ∘ H.symm
  let Y := fun q : PuncturedPeriodTorus L => full q.1
  change ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H → ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm → MarkedHelicoidalEndForms L Y
  intro hH hi
  have eq : puncturedTorusPullback L Y = full ∘ periodTorusProjection L := by
    funext z
    by_cases h : z ∈ L.lattice
    · have atzero : H.symm 0 = OnePoint.infty := H.symm_apply_eq.mpr h0.symm
      simp [puncturedTorusPullback,h,(periodTorusProjection_eq_zero L z).mpr h,full,atzero,Z]
    · simp [puncturedTorusPullback,h,Y,puncturedPlaneProjection]
  have reg := marked_harmonic_immersion_coordinates E X 0 hchart hm H h0 hH hi
  have extreg := exterior_immersion_eventually_differentiable X hchart A.holomorphic A.target
  have hh : ∀ᶠ ζ in cobounded ℂ, X (e.symm ζ) 2 = A.heightOffset+ζ.re := by
    filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop A.radius)] with ζ hz
    have hζ : ζ ∈ e.target := A.target ▸ hz
    rw [A.height _ (e.map_target hζ),e.right_inv hζ]
  have orders := compactified_exterior_surface_end_poles X e A.positive A.target A.core hesc
    A.heightOffset A.pitch A.pitch_ne A.correction A.analytic extreg hh A.gauss 0
  have hrr := compactified_exterior_end_regular X e A.positive A.target A.core hesc
    A.pitch A.correction A.analytic extreg A.gauss 0
  have hχ : E.filledChart ∈ atlas ℂ (OnePoint M) := Or.inr rfl
  have marked := uniformized_torus_actual_end_orders H OnePoint.infty h0 hH hi E.filledChart
    (IsManifold.subset_maximalAtlas hχ) OnePoint.infty_notMem_image_coe rfl Z hrr orders.1 orders.2.2.1
  have expansion := uniformized_actual_gauss_end_residue H OnePoint.infty h0 hH hi E.filledChart
    (IsManifold.subset_maximalAtlas hχ) OnePoint.infty_notMem_image_coe rfl Z (hrr.mono fun _ h => h.1)
    (mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr A.pitch_ne)) A.analytic
    (filled_exterior_gauss_exponential X A hesc extreg 0)
  refine ⟨?_,?_,?_⟩
  · rw [eq]
    exact reg
  · change meromorphicOrderAt (fun z => immersionComplexCoefficient (puncturedTorusPullback L Y) z 2) 0 = _
    rw [eq]
    exact marked.2.1.trans orders.2.1
  · change ∃ (κ : ℂ) (R : ℂ → ℂ), κ ≠ 0 ∧ AnalyticAt ℂ R 0 ∧
      ∀ᶠ z in 𝓝[≠] (0:ℂ), logDeriv (immersionGaussMap (puncturedTorusPullback L Y)) z = κ/z^2+R z
    rw [eq]
    exact expansion

/-- Starting with the original conformal punctured surface, the exterior
height and Gauss chart, and genus-one uniformization, construct one
biholomorphic marking carrying both the immersion and its residue-free
logarithmic Gauss pole. No symmetry or interior Gauss data are assumed. -/
theorem original_exterior_surface_marked_end_forms {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (uniform : CompactGenusOneUniformization.{u} L₀)
    (X : M → Fin 3 → ℝ) (hX : IsClosedEmbedding X) (hchart : ∀ d ∈ atlas ℂ M, HarmonicImmersionChart X d)
    (A : GeometricExteriorCoordinate X) :
    ∃ (L : PeriodPair) (f : M ≃ₜ PuncturedPeriodTorus L) (Y : PuncturedPeriodTorus L → Fin 3 → ℝ),
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f.symm ∧
      (∀ x, Y (f x) = X x) ∧ IsClosedEmbedding Y ∧ MarkedHelicoidalEndForms L Y := by
  let e := A.chart
  have tails := homeomorphic_punctured_surface_connected_tails (0:PeriodTorus L₀) top
  have hc : Continuous (fun x => X x 2) := (continuous_apply 2).comp hX.continuous
  have hnc : NoncompactSpace M := noncompact_of_exterior_height e A.target _ hc A.heightOffset A.height
  have hlc : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ℂ M
  have hesc := true_exterior_height_coordinate_escapes tails e A.target A.core _ hc A.heightOffset A.height
  let E := exteriorCoordinateComplexEnd e A.positive A.target A.core hesc
  let _ := compactifiedEndAtlas E
  have hm := (exteriorCoordinate_fills_complex_manifold e A.positive A.target A.core hesc A.holomorphic).1
  have hcm : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) := hm
  let ht := top.onePointCongr.trans (punctureCompactification (0:PeriodTorus L₀))
  obtain ⟨L,H,h0,hH,hi,hf,hir⟩ := compactified_uniformization_restricts E (uniform (OnePoint M) ⟨ht⟩)
  let f := markedPuncturedUniformization H h0
  let Y := fun q : PuncturedPeriodTorus L => (H.symm q.1).elim (0:Fin 3 → ℝ) X
  refine ⟨L,f,Y,hf,hir,?_,(marked_immersion_closedEmbedding_range H h0 X hX 0).1,
    exterior_forms_in_pointed_filling X hchart A hesc H h0 hH hi⟩
  intro x
  change (H.symm (H (x:OnePoint M))).elim 0 X=X x
  rw [H.symm_apply_apply]
  rfl

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exterior_forms_in_pointed_filling
#print axioms TwoAxisHelicoid.original_exterior_surface_marked_end_forms
