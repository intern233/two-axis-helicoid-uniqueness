import TwoAxisHelicoid.HelicoidGraphExteriorMetric
import TwoAxisHelicoid.AlignedGaussLogGerm
import TwoAxisHelicoid.ComplexEndOnePointCharts

namespace TwoAxisHelicoid
open Complex Real Set Filter
open scoped Topology ContDiff

theorem helicoidProjectedComplexParameter_contDiffAt {y : HelicoidTubeCoordinates}
    (hy : y∈helicoidTubeEquiv.target) : ContDiffAt ℝ 1 helicoidProjectedComplexParameter y := by
  have h : ContDiff ℝ 1 helicoidConformalBaseHomeomorph.symm :=
    Complex.equivRealProdCLM.symm.contDiff.comp ((Real.contDiff_arsinh.comp contDiff_fst).prodMk contDiff_snd)
  exact h.contDiffAt.comp y ((helicoidBaseCoordinates_contDiffAt hy).of_le (by simp))

/-- In a given isothermal chart of a proper C¹ helicoidal graph, the
reciprocal natural coordinate is a smooth germ away from the puncture.
Both sides of its metric inequality follow from the actual graph. -/
theorem HasHelicoidC1End.reciprocal_projection_metric {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (graph : HasHelicoidC1End X) (proper : IsProperMap X)
    (E : PuncturedComplexEnd M)
    (smooth : ∀ᶠ z in 𝓝[≠] (0:ℂ), ContDiffAt ℝ 1 (X ∘ E.coord.symm) z)
    (iso : ∀ᶠ z in 𝓝[≠] (0:ℂ), ∃ c : ℝ, 0<c ∧ ∀ v : ℂ,
      (∑ j, (tubeCartesian (fderiv ℝ (X ∘ E.coord.symm) z v) j)^2)=c*‖v‖^2) :
    let F := fun z => (helicoidProjectedComplexParameter (X (E.coord.symm z)))⁻¹
    ∀ᶠ z in 𝓝[≠] (0:ℂ), ContDiffAt ℝ 1 F z ∧
      ∃ m c : ℝ, 0<m ∧ 0<c ∧ ∀ v : ℂ,
        m*‖fderiv ℝ F z v‖^2/4≤c*‖v‖^2 ∧ c*‖v‖^2≤4*(m*‖fderiv ℝ F z v‖^2) := by
  let Y := X ∘ E.coord.symm
  let P := helicoidProjectedComplexParameter ∘ Y
  let F := fun z => (P z)⁻¹
  obtain ⟨u,B,data⟩ := graph.exterior_conformal_graph proper.continuous
  let G := helicoidGraphMap u ∘ helicoidConformalBase
  have normY : Tendsto (fun z => ‖Y z‖) (𝓝[≠] (0:ℂ)) atTop :=
    (tendsto_norm_cocompact_atTop.comp (isProperMap_iff_tendsto_cocompact.mp proper).2).comp E.from_zero
  have ev : ∀ᶠ z in 𝓝[≠] (0:ℂ), 2<‖P z‖ ∧ DifferentiableAt ℝ u (helicoidConformalBase (P z)) ∧
      |u (helicoidConformalBase (P z))|≤1/2 ∧ helicoidGraphGradientNorm u (helicoidConformalBase (P z))≤1/2 ∧
      Y z=G (P z) ∧ Y z∈helicoidTubeEquiv.target := by
    filter_upwards [normY.eventually_gt_atTop B] with z hz
    obtain ⟨w,hw,du,sz,gr,eq⟩ := data (Y z) (mem_range_self (E.coord.symm z)) hz
    have fact := helicoidProjectedComplexParameter_graph (sz.trans_lt (by norm_num))
    have id : P z=w := (congrArg helicoidProjectedComplexParameter eq).trans fact.2
    rw [id]
    exact ⟨hw,du,sz,gr,eq,eq ▸ fact.1⟩
  have same : Y =ᶠ[𝓝[≠] (0:ℂ)] G ∘ P := ev.mono fun _ h => h.2.2.2.2.1
  filter_upwards [ev,punctured_germ_eventually_local same,smooth,iso] with z h coincidence sy eq
  obtain ⟨far,du,sz,gr,_,tube⟩ := h
  obtain ⟨c,hc,conf⟩ := eq
  have sp : ContDiffAt ℝ 1 P z := (helicoidProjectedComplexParameter_contDiffAt tube).comp z sy
  have nz := norm_pos_iff.mp ((by norm_num : (0:ℝ)<2).trans far)
  have si : ContDiffAt ℝ 1 F z := sp.inv nz
  have gd := (helicoidGraphMap_differentiableAt du).comp (P z) (helicoidConformalBase_hasFDerivAt _).differentiableAt
  have d : fderiv ℝ Y z=(fderiv ℝ G (P z)).comp (fderiv ℝ P z) :=
    coincidence.fderiv_eq.trans (fderiv_comp z gd (sp.differentiableAt one_ne_zero))
  let a : ℂ := -((P z)^2)⁻¹
  have dInv := ((hasDerivAt_inv nz).hasFDerivAt.restrictScalars ℝ).comp z (sp.differentiableAt one_ne_zero).hasFDerivAt
  have df (v : ℂ) : fderiv ℝ F z v=fderiv ℝ P z v*a :=
    congrArg (fun D : ℂ →L[ℝ] ℂ => D v) dInv.fderiv
  have apos : 0<‖a‖^2 := pow_pos (norm_pos_iff.mpr (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 nz)))) 2
  refine ⟨si,(Real.cosh (P z).re)^2,c*‖a‖^2,by positivity,mul_pos hc apos,?_⟩
  intro v
  have mt := helicoid_conformal_graph_metric_bounds du sz gr (fderiv ℝ P z v)
  have cv := conf v
  change (∑ j, (tubeCartesian (fderiv ℝ Y z v) j)^2)=c*‖v‖^2 at cv
  rw [d,ContinuousLinearMap.comp_apply] at cv
  change _≤(∑ j, (tubeCartesian (fderiv ℝ G (P z) (fderiv ℝ P z v)) j)^2) ∧ _≤_ at mt
  rw [cv] at mt
  change (Real.cosh (P z).re)^2*‖fderiv ℝ F z v‖^2/4≤(c*‖a‖^2)*‖v‖^2 ∧ _≤4*((Real.cosh (P z).re)^2*‖fderiv ℝ F z v‖^2)
  rw [df,norm_mul,mul_pow]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right mt.1 apos.le,mul_le_mul_of_nonneg_right mt.2 apos.le]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasHelicoidC1End.reciprocal_projection_metric
