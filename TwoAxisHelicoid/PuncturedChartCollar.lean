import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology
open scoped Topology

/-- Radially push a point of a punctured chart out to a collar. -/
noncomputable def chartCollarPoint (c : ℂ) (r s : ℝ) (z : ℂ) : ℂ :=
  c + (max ‖z-c‖ (s*r)/‖z-c‖) • (z-c)

theorem chartCollarPoint_dist {c z : ℂ} (hz : z ≠ c) (r s : ℝ) :
    dist (chartCollarPoint c r s z) c = max ‖z-c‖ (s*r) := by
  have hn := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  simp only [chartCollarPoint,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs]
  rw [abs_of_nonneg (div_nonneg (le_trans hn.le (le_max_left _ _)) hn.le),div_mul_cancel₀ _ hn.ne']

theorem chartCollarPoint_ne {c z : ℂ} (hz : z ≠ c) (r s : ℝ) : chartCollarPoint c r s z ≠ c := by
  apply dist_pos.mp
  rw [chartCollarPoint_dist hz]
  exact lt_of_lt_of_le (norm_pos_iff.mpr (sub_ne_zero.mpr hz)) (le_max_left _ _)

theorem chartCollarPoint_fixed {c z : ℂ} {r s : ℝ} (hz : z ≠ c) (h : s*r ≤ ‖z-c‖) :
    chartCollarPoint c r s z = z := by
  rw [chartCollarPoint,max_eq_left h,div_self (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)),one_smul,add_sub_cancel]

theorem chartCollarPoint_target {T : Set ℂ} {c z : ℂ} {r : ℝ} (hr : 0 < r) (hz : z ≠ c)
    (hzT : z ∈ T) (hB : closedBall c r ⊆ T) (s : unitInterval) : chartCollarPoint c r s.1 z ∈ T := by
  by_cases hinside : ‖z-c‖ ≤ r
  · apply hB
    rw [mem_closedBall,chartCollarPoint_dist hz]
    exact max_le hinside (by simpa only [one_mul] using mul_le_mul_of_nonneg_right s.2.2 hr.le)
  · rw [chartCollarPoint_fixed hz]
    · exact hzT
    · exact (show s.1*r ≤ r by simpa only [one_mul] using mul_le_mul_of_nonneg_right s.2.2 hr.le).trans (le_of_not_ge hinside)

theorem chartCollarPoint_continuousAt {W : Type*} [TopologicalSpace W] {u : W → ℝ} {f : W → ℂ}
    {c : ℂ} {r : ℝ} {p : W} (hu : ContinuousAt u p) (hf : ContinuousAt f p) (hn : f p ≠ c) :
    ContinuousAt (fun w => chartCollarPoint c r (u w) (f w)) p := by
  have h := hf.sub (continuousAt_const (y := c))
  exact continuousAt_const.add (((h.norm.max (hu.mul continuousAt_const)).div h.norm
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hn))).smul h)

variable {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M ℂ) {p : M} (hp : p ∈ e.source)
    {r : ℝ} (hr : 0 < r) (hB : closedBall (e p) r ⊆ e.target)

noncomputable def chartCollarMap (p : M) (r : ℝ) (s : unitInterval) (x : M) : M := by
  classical
  exact if x ∈ e.source then e.symm (chartCollarPoint (e p) r s.1 (e x)) else x

include hp hr hB in
theorem chartCollarMap_nonpuncture (s : unitInterval) {x : M} (hx : x ≠ p) : chartCollarMap e p r s x ≠ p := by
  classical
  by_cases hs : x ∈ e.source
  · have hxc : e x ≠ e p := fun h => hx (e.injOn hs hp h)
    have ht := chartCollarPoint_target hr hxc (e.map_source hs) hB s
    intro he
    have he' := congrArg e he
    simp only [chartCollarMap,hs,ite_true,e.right_inv ht] at he'
    exact chartCollarPoint_ne hxc r s.1 he'
  · simpa only [chartCollarMap,hs,ite_false] using hx

include hr in
theorem chartCollarMap_outside_closed (s : unitInterval) {x : M} (hx : x ∉ e.symm '' closedBall (e p) r) :
    chartCollarMap e p r s x = x := by
  classical
  by_cases hs : x ∈ e.source
  · have hn : ¬ ‖e x-e p‖ ≤ r := fun h => hx ⟨e x,by rwa [mem_closedBall,dist_eq_norm],e.left_inv hs⟩
    have hn' : e x ≠ e p := fun h => hn (by rw [h,sub_self,norm_zero]; exact hr.le)
    have hsr : s.1*r ≤ r := by simpa only [one_mul] using mul_le_mul_of_nonneg_right s.2.2 hr.le
    have hl := hsr.trans (le_of_not_ge hn)
    simp only [chartCollarMap,hs,ite_true,chartCollarPoint_fixed hn' hl,e.left_inv hs]
  · simp [chartCollarMap,hs]

include hp hr hB in
theorem chartCollarMap_joint_continuous [T2Space M] :
    Continuous (fun u : unitInterval × {x : M // x ≠ p} => chartCollarMap e p r u.1 u.2.1) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro u
  have hx := continuous_subtype_val.comp (continuous_snd (X := unitInterval) (Y := {x : M // x ≠ p}))
  have hs := continuous_subtype_val.comp (continuous_fst (X := unitInterval) (Y := {x : M // x ≠ p}))
  by_cases he : u.2.1 ∈ e.source
  · have hn : e u.2.1 ≠ e p := fun h => u.2.2 (e.injOn he hp h)
    have hc := chartCollarPoint_continuousAt (r := r) (c := e p) (p := u)
      (u := fun w : unitInterval × {x : M // x ≠ p} => w.1.1) (f := fun w => e w.2.1)
      hs.continuousAt ((e.continuousAt he).comp (f := fun w : unitInterval × {x : M // x ≠ p} => w.2.1) hx.continuousAt) hn
    have ht := chartCollarPoint_target hr hn (e.map_source he) hB u.1
    apply ((e.symm.continuousAt ht).comp (f := fun w : unitInterval × {x : M // x ≠ p} => chartCollarPoint (e p) r w.1.1 (e w.2.1)) hc).congr_of_eventuallyEq
    filter_upwards [hx.continuousAt.eventually (e.open_source.mem_nhds he)] with y hy
    change y.2.1 ∈ e.source at hy
    simp only [chartCollarMap,hy,ite_true,Function.comp_apply]
  · have hK : IsClosed (e.symm '' closedBall (e p) r) :=
      ((isCompact_closedBall (e p) r).image_of_continuousOn (e.continuousOn_symm.mono hB)).isClosed
    have hu : u.2.1 ∉ e.symm '' closedBall (e p) r := by
      rintro ⟨w,hw,hwu⟩
      exact he (hwu ▸ e.map_target (hB hw))
    apply hx.continuousAt.congr_of_eventuallyEq
    filter_upwards [hx.continuousAt.eventually (hK.isOpen_compl.mem_nhds hu)] with y hy
    exact chartCollarMap_outside_closed e hr y.1 hy

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.chartCollarMap_joint_continuous
