import TwoAxisHelicoid.HelicoidNaturalPuncture
import TwoAxisHelicoid.HelicoidHeightPoleDegree
import TwoAxisHelicoid.HelicoidGraphSpatialGrowth

namespace TwoAxisHelicoid
open Complex Set Filter Metric Bornology
open scoped Topology

/-- In any chosen end chart, the actual normal graph above the central
vertical ruling supplies a continuous tail approaching the puncture.
Its projected angle is the parameter and its spatial height differs
from this parameter by at most one. -/
theorem HasHelicoidC1End.center_puncture_ray {M : Type*} [TopologicalSpace M]
    [T2Space M] [WeaklyLocallyCompactSpace M] [NoncompactSpace M]
    {X : M → HelicoidTubeCoordinates} (graph : HasHelicoidC1End X) (proper : IsProperMap X)
    (E : PuncturedComplexEnd M) :
    ∃ p : ℝ → ℂ, Tendsto p atTop (𝓝[≠] 0) ∧ ∀ᶠ t in atTop,
      ContinuousAt p t ∧ helicoidProjectedComplexParameter (X (E.coord.symm (p t)))=(t:ℂ)*I ∧
      |(X (E.coord.symm (p t))).2-t|≤1 := by
  obtain ⟨D,relation⟩ := graph.natural_puncture_coordinate proper
  let v := fun t : ℝ => (t:ℂ)*I
  let w := fun t : ℝ => (v t)⁻¹
  have large : Tendsto (fun t => ‖v t‖) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro r
    filter_upwards [eventually_ge_atTop (max r 1)] with t h
    rw [show ‖v t‖=|t| by simp [v],abs_of_pos (by linarith [le_max_right r 1])]
    exact (le_max_left _ _).trans h
  have limit : Tendsto w atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.mp large),?_⟩
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t h
    exact inv_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr h.ne') I_ne_zero)
  let q := D.coord.symm ∘ w
  have esc : Tendsto q atTop (cocompact M) := D.from_zero.comp limit
  let p := E.coord ∘ q
  have Esource : E.coord.source∈cocompact M := by simpa only [compl_compl] using E.compact_core.compl_mem_cocompact
  have Dtarget : D.coord.target∈𝓝[≠] (0:ℂ) := by
    rw [D.target_eq]
    exact inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) D.radius_pos)) self_mem_nhdsWithin
  refine ⟨p,E.to_punctured_zero.comp esc,?_⟩
  filter_upwards [limit.eventually Dtarget,esc.eventually Esource,esc.eventually relation,eventually_gt_atTop (0:ℝ)] with t ht he hr pos
  have nz : v t≠0 := mul_ne_zero (ofReal_ne_zero.mpr pos.ne') I_ne_zero
  have cont : ContinuousAt w t := ((Complex.continuous_ofReal.continuousAt.mul continuousAt_const).inv₀ nz)
  have cq : ContinuousAt q t := (D.coord.symm.continuousAt ht).comp cont
  have pr : helicoidProjectedComplexParameter (X (q t))=v t := by
    have a := hr.1
    change D.coord (D.coord.symm (w t))=_ at a
    rw [D.coord.right_inv ht] at a
    exact inv_injective a.symm
  have left : E.coord.symm (p t)=q t := E.coord.left_inv he
  refine ⟨(E.coord.continuousAt he).comp cq,by rwa [left],?_⟩
  rw [left]
  have r := hr.2
  rw [pr] at r
  simpa [v] using r

/-- Uniform bounds for the graph and its first derivatives in the
same graph coordinate used to compute the pointwise tangent plane. -/
theorem HasHelicoidC1End.eventually_graph_with_slope {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (graph : HasHelicoidC1End X) (proper : IsProperMap X) :
    let P := helicoidProjectedComplexParameter ∘ X
    ∃ u : ℝ × ℝ → ℝ, ∀ᶠ x in cocompact M,
      DifferentiableAt ℝ u (helicoidConformalBase (P x)) ∧ |u (helicoidConformalBase (P x))|≤1/2 ∧
      helicoidGraphGradientNorm u (helicoidConformalBase (P x))≤1/2 ∧
      X x=helicoidGraphMap u (helicoidConformalBase (P x)) ∧ X x∈helicoidTubeEquiv.target := by
  obtain ⟨u,B,h⟩ := graph.exterior_conformal_graph proper.continuous
  have esc := tendsto_norm_cocompact_atTop.comp (isProperMap_iff_tendsto_cocompact.mp proper).2
  refine ⟨u,?_⟩
  filter_upwards [esc.eventually_gt_atTop B] with x hx
  obtain ⟨z,_,du,small,gradient,sp⟩ := h (X x) (mem_range_self x) hx
  have t := helicoidProjectedComplexParameter_graph (small.trans_lt (by norm_num))
  have eq : (helicoidProjectedComplexParameter ∘ X) x=z := (congrArg helicoidProjectedComplexParameter sp).trans t.2
  rw [eq]
  exact ⟨du,small,gradient,sp,sp ▸ t.1⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasHelicoidC1End.center_puncture_ray
#print axioms TwoAxisHelicoid.HasHelicoidC1End.eventually_graph_with_slope
