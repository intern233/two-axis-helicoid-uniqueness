import TwoAxisHelicoid.PuncturedChartCollar
import TwoAxisHelicoid.CompactCoreCollapseExtension

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology
open scoped Topology

noncomputable def chartPinchFactor (r : ℝ) (c z : ℂ) : ℝ := max 0 (min 1 ((dist z c-r)/r))
noncomputable def chartPinchPoint (r : ℝ) (c z : ℂ) : ℂ := c+chartPinchFactor r c z • (z-c)

private theorem chartPinchPoint_inner {r : ℝ} (hr : 0 < r) {c z : ℂ} (hz : dist z c ≤ r) :
    chartPinchPoint r c z = c := by
  have h : (dist z c-r)/r ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hz) hr.le
  simp only [chartPinchPoint,chartPinchFactor,max_eq_left ((min_le_right _ _).trans h),zero_smul,add_zero]

private theorem chartPinchPoint_outer {r : ℝ} (hr : 0 < r) {c z : ℂ} (hz : 2*r ≤ dist z c) :
    chartPinchPoint r c z = z := by
  have h : 1 ≤ (dist z c-r)/r := (le_div_iff₀ hr).mpr (by linarith)
  simp [chartPinchPoint,chartPinchFactor,min_eq_left h]

private theorem chartPinchPoint_dist_le (r : ℝ) (c z : ℂ) : dist (chartPinchPoint r c z) c ≤ dist z c := by
  have h₀ : 0 ≤ chartPinchFactor r c z := le_max_left ..
  have h₁ : chartPinchFactor r c z ≤ 1 := max_le zero_le_one (min_le_left ..)
  simp only [chartPinchPoint,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg h₀]
  exact mul_le_of_le_one_left (norm_nonneg _) h₁

variable {T : Type*} [TopologicalSpace T] (e : OpenPartialHomeomorph T ℂ) (p : T) (r : ℝ)

noncomputable def chartPinchMap (x : T) : T := by
  classical
  exact if x ∈ e.source then e.symm (chartPinchPoint r (e p) (e x)) else x

variable {e p r}

theorem chartPinchMap_inner (hp : p ∈ e.source) (hr : 0 < r)
    (hB : closedBall (e p) (2*r) ⊆ e.target) {x : T} (hx : x ∈ e.symm '' closedBall (e p) r) :
    chartPinchMap e p r x = p := by
  classical
  obtain ⟨z,hz,rfl⟩ := hx
  have ht := hB ((closedBall_subset_closedBall (by linarith : r ≤ 2*r)) hz)
  simp only [chartPinchMap,e.map_target ht,ite_true,e.right_inv ht,chartPinchPoint_inner hr hz,e.left_inv hp]

theorem chartPinchMap_outer (hr : 0 < r) {x : T} (hx : x ∉ e.symm '' ball (e p) (2*r)) :
    chartPinchMap e p r x = x := by
  classical
  by_cases hs : x ∈ e.source
  · have h : 2*r ≤ dist (e x) (e p) := le_of_not_gt fun h => hx ⟨e x,h,e.left_inv hs⟩
    simp [chartPinchMap,hs,chartPinchPoint_outer hr h,e.left_inv hs]
  · simp [chartPinchMap,hs]

theorem chartPinchMap_continuous [T2Space T] (hr : 0 < r) (hB : closedBall (e p) (2*r) ⊆ e.target) :
    Continuous (chartPinchMap e p r) := by
  classical
  have hK := ((isCompact_closedBall (e p) (2*r)).image_of_continuousOn (e.continuousOn_symm.mono hB)).isClosed
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hs : x ∈ e.source
  · have ht : chartPinchPoint r (e p) (e x) ∈ e.target := by
      by_cases h : 2*r ≤ dist (e x) (e p)
      · rw [chartPinchPoint_outer hr h]; exact e.map_source hs
      · exact hB ((chartPinchPoint_dist_le _ _ _).trans (le_of_not_ge h))
    have hF : Continuous (chartPinchPoint r (e p)) := by unfold chartPinchPoint chartPinchFactor; fun_prop
    have h₁ : ContinuousAt (chartPinchPoint r (e p) ∘ (e : T → ℂ)) x :=
      (hF.continuousAt (x := e x)).comp (e.continuousAt hs)
    have h₂ : ContinuousAt ((e.symm : ℂ → T) ∘ (chartPinchPoint r (e p) ∘ (e : T → ℂ))) x :=
      ContinuousAt.comp (f := chartPinchPoint r (e p) ∘ (e : T → ℂ)) (x := x) (e.symm.continuousAt ht) h₁
    apply h₂.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hs] with y hy
    simp [chartPinchMap,hy]
  · have hx : x ∉ e.symm '' closedBall (e p) (2*r) := by
      rintro ⟨u,hu,rfl⟩
      exact hs (e.map_target (hB hu))
    apply continuousAt_id.congr_of_eventuallyEq
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
    exact chartPinchMap_outer hr (fun h => hy ((image_mono ball_subset_closedBall) h))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.chartPinchMap_continuous
