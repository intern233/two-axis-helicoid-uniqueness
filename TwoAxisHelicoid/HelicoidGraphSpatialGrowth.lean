import TwoAxisHelicoid.HelicoidIntrinsicHeightOrders
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace TwoAxisHelicoid
open Complex Real Set Filter Metric
open scoped Topology

theorem HasHelicoidC1End.eventually_natural_graph {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (graph : HasHelicoidC1End X) (proper : IsProperMap X) :
    let P := helicoidProjectedComplexParameter ∘ X
    ∃ u : ℝ × ℝ → ℝ, ∀ᶠ x in cocompact M, 2<‖P x‖ ∧
      DifferentiableAt ℝ u (helicoidConformalBase (P x)) ∧ |u (helicoidConformalBase (P x))|≤1/2 ∧
      X x=helicoidGraphMap u (helicoidConformalBase (P x)) ∧ X x∈helicoidTubeEquiv.target := by
  obtain ⟨u,B,h⟩ := graph.exterior_conformal_graph proper.continuous
  have esc := tendsto_norm_cocompact_atTop.comp (isProperMap_iff_tendsto_cocompact.mp proper).2
  refine ⟨u,?_⟩
  filter_upwards [esc.eventually_gt_atTop B] with x hx
  obtain ⟨z,large,du,small,_,sp⟩ := h (X x) (mem_range_self x) hx
  have t := helicoidProjectedComplexParameter_graph (small.trans_lt (by norm_num))
  have eq : (helicoidProjectedComplexParameter ∘ X) x=z := (congrArg helicoidProjectedComplexParameter sp).trans t.2
  rw [eq]
  exact ⟨large,du,small,sp,sp ▸ t.1⟩

/-- All three physical Cartesian coordinates of a bounded normal graph
grow at most exponentially in the natural helicoid parameter. -/
theorem helicoid_natural_spatial_bound {s : ℝ} (hs : |s|≤1) (z : ℂ) :
    ‖helicoidTubeMap ((s,Real.sinh z.re),z.im)‖≤2*Real.exp ‖z‖ := by
  let r := Real.sinh z.re
  let θ := z.im
  let B := Real.exp ‖z‖
  have b1 : 1≤B := Real.one_le_exp (norm_nonneg z)
  have rb : |r|≤B := by
    rw [show |r|=Real.sinh |z.re| from Real.abs_sinh _]
    rw [Real.sinh_eq]
    have e := Real.exp_le_exp.mpr (Complex.abs_re_le_norm z)
    linarith [Real.exp_pos (-|z.re|),Real.exp_pos |z.re|]
  have sb : |s/helicoidQ r|≤1 := by
    rw [abs_div,abs_of_pos (helicoidQ_pos r),div_le_iff₀ (helicoidQ_pos r),one_mul]
    exact hs.trans (helicoidQ_ge_one r)
  have trig (v : ℝ) (hv : |v|≤1) : |r*v|≤B ∧ |(s/helicoidQ r)*v|≤1 := by
    rw [abs_mul,abs_mul]
    constructor
    · exact ((mul_le_mul_of_nonneg_left hv (abs_nonneg r)).trans_eq (mul_one _)).trans rb
    · exact ((mul_le_mul_of_nonneg_left hv (abs_nonneg _)).trans_eq (mul_one _)).trans sb
  have a := trig (Real.cos θ) (abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩)
  have b := trig (Real.sin θ) (abs_le.mpr ⟨Real.neg_one_le_sin _,Real.sin_le_one _⟩)
  have hθ : |θ|≤B := (Complex.abs_im_le_norm z).trans (by linarith [Real.add_one_le_exp ‖z‖])
  change max (max ‖r*Real.cos θ+s/helicoidQ r*Real.sin θ‖ ‖r*Real.sin θ-s/helicoidQ r*Real.cos θ‖)
    ‖θ+helicoidAngle r s‖≤2*B
  simp only [Real.norm_eq_abs,max_le_iff]
  exact ⟨⟨(abs_add_le _ _).trans (by linarith [a.1,b.2]),(abs_sub _ _).trans (by linarith [b.1,a.2])⟩,
    (abs_add_le _ _).trans (by linarith [helicoidAngle_abs_le (r := r) hs])⟩

theorem HasHelicoidC1End.isothermal_spatial_growth {M : Type*} [TopologicalSpace M]
    [T2Space M] [WeaklyLocallyCompactSpace M] [NoncompactSpace M]
    {X : M → HelicoidTubeCoordinates} (graph : HasHelicoidC1End X) (proper : IsProperMap X)
    (E : PuncturedComplexEnd M)
    (smooth : ∀ᶠ z in 𝓝[≠] (0:ℂ), ContDiffAt ℝ 1 (X ∘ E.coord.symm) z)
    (iso : ∀ᶠ z in 𝓝[≠] (0:ℂ), ∃ c : ℝ, 0<c ∧ ∀ v : ℂ,
      (∑ j, (tubeCartesian (fderiv ℝ (X ∘ E.coord.symm) z v) j)^2)=c*‖v‖^2) :
    ∃ N : ℕ, 0<N ∧ ∃ C : ℝ, 0<C ∧ ∀ᶠ z in 𝓝[≠] (0:ℂ),
      ‖X (E.coord.symm z)‖≤2*Real.exp (C/‖z‖^N) := by
  obtain ⟨N,hN,C,hC,bound⟩ := graph.natural_parameter_polynomial_growth proper E smooth iso
  obtain ⟨u,actual⟩ := graph.eventually_natural_graph proper
  refine ⟨N,hN,C,hC,?_⟩
  filter_upwards [bound,E.from_zero.eventually actual] with z h g
  let p := helicoidProjectedComplexParameter (X (E.coord.symm z))
  obtain ⟨_,_,small,eq,_⟩ := g
  rw [eq]
  exact (helicoid_natural_spatial_bound (small.trans (by norm_num)) p).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h.1) (by norm_num))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasHelicoidC1End.isothermal_spatial_growth
