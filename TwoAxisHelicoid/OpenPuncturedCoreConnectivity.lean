import TwoAxisHelicoid.MarkedCoreCollapseMap
import TwoAxisHelicoid.PuncturedLatticePlane
import TwoAxisHelicoid.PeriodTorusTopology
import Mathlib.Topology.Connected.PathConnected

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology
open scoped Topology

theorem punctured_torus_is_path_connected (A : PeriodPair) : PathConnectedSpace (PuncturedPeriodTorus A) := by
  let : PathConnectedSpace (PuncturedLatticePlane A) := isPathConnected_iff_pathConnectedSpace.mp
    (Set.Countable.isPathConnected_compl_of_one_lt_rank (by simp) (countable_of_Lindelof_of_discrete (X := A.lattice)))
  exact (puncturedPlaneProjection_surjective A).pathConnectedSpace (puncturedPlaneProjection_continuous A)

private theorem collar_avoids_smaller_disk {T : Type*} [TopologicalSpace T] (e : OpenPartialHomeomorph T ℂ)
    {p x : T} (hp : p ∈ e.source) (hx : x ≠ p) {a b : ℝ} (hab : a < b) (hb : 0 < b)
    (hB : closedBall (e p) b ⊆ e.target) : chartCollarMap e p b 1 x ∉ e.symm '' closedBall (e p) a := by
  rintro ⟨w,hw,he⟩
  have ht := hB (closedBall_subset_closedBall hab.le hw)
  by_cases hs : x ∈ e.source
  · have hn : e x ≠ e p := fun h => hx (e.injOn hs hp h)
    have hT := chartCollarPoint_target hb hn (e.map_source hs) hB (1:unitInterval)
    have heq := congrArg e he
    simp only [chartCollarMap,hs,ite_true,e.right_inv ht,e.right_inv hT] at heq
    change w = chartCollarPoint (e p) b (1:ℝ) (e x) at heq
    have h := hw
    rw [mem_closedBall,heq,chartCollarPoint_dist hn,one_mul] at h
    exact hab.not_ge ((le_max_right ..).trans h)
  · simp only [chartCollarMap,hs,ite_false] at he
    exact hs (he ▸ e.map_target ht)

private theorem outside_slightly_larger_disk {T : Type*} [TopologicalSpace T] (e : OpenPartialHomeomorph T ℂ)
    {p x : T} {r : ℝ} (hr : 0 < r) (hB : closedBall (e p) (2*r) ⊆ e.target)
    (hx : x ∈ openChartCore e p r) : ∃ d : ℝ, r/2 < d ∧ d ≤ 2*r ∧ x ∉ e.symm '' closedBall (e p) d := by
  by_cases hs : x ∈ e.source
  · have hd : r/2 < dist (e x) (e p) := lt_of_not_ge (fun h => hx ⟨e x,h,e.left_inv hs⟩)
    let d := min r ((r/2+dist (e x) (e p))/2)
    have hb : d ≤ 2*r := (min_le_left ..).trans (by linarith)
    refine ⟨d,lt_min (half_lt_self hr) (by linarith),hb,?_⟩
    rintro ⟨w,hw,he⟩
    have heq : w = e x := (e.right_inv (hB (closedBall_subset_closedBall hb hw))).symm.trans (congrArg e he)
    have hlt : d < dist (e x) (e p) := (min_le_right ..).trans_lt (by linarith)
    exact hlt.not_ge (heq ▸ hw)
  · refine ⟨r,half_lt_self hr,by linarith,?_⟩
    rintro ⟨w,hw,he⟩
    exact hs (he ▸ e.map_target (hB (closedBall_subset_closedBall (by linarith : r ≤ 2*r) hw)))

/-- Removing a small closed disk instead of just the puncture preserves
path connectedness: an actual joining path is pushed outside a slightly
larger disk while fixing its two chosen endpoints. -/
theorem open_chart_core_path_connected {T : Type*} [TopologicalSpace T] [T2Space T]
    (e : OpenPartialHomeomorph T ℂ) {p : T} (hp : p ∈ e.source) {r : ℝ} (hr : 0 < r)
    (hB : closedBall (e p) (2*r) ⊆ e.target) (hne : Nonempty (openChartCore e p r))
    (hpunc : PathConnectedSpace {x : T // x ≠ p}) : PathConnectedSpace (openChartCore e p r) := by
  let := hpunc
  refine ⟨hne,fun x y => ?_⟩
  obtain ⟨a,ha,ha₂,hxa⟩ := outside_slightly_larger_disk e hr hB x.2
  obtain ⟨b,hb,_,hyb⟩ := outside_slightly_larger_disk e hr hB y.2
  let d := min a b
  have hd : r/2 < d := lt_min ha hb
  have hdpos : 0 < d := (half_pos hr).trans hd
  have hD : closedBall (e p) d ⊆ e.target := (closedBall_subset_closedBall ((min_le_left ..).trans ha₂)).trans hB
  have H (q : {z : T // z ≠ p}) : chartCollarMap e p d 1 q.1 ∈ openChartCore e p r :=
    collar_avoids_smaller_disk e hp q.2 hd hdpos hD
  let f := fun q : {z : T // z ≠ p} => (⟨_,H q⟩ : openChartCore e p r)
  have hc : Continuous f :=
    ((chartCollarMap_joint_continuous e hp hdpos hD).comp (continuous_const.prodMk continuous_id)).subtype_mk _
  have H0 (q : openChartCore e p r) : q.1 ≠ p := fun he => q.2 ⟨e p,mem_closedBall_self (half_pos hr).le,(e.left_inv hp).trans he.symm⟩
  let x' : {z : T // z ≠ p} := ⟨x.1,H0 x⟩
  let y' : {z : T // z ≠ p} := ⟨y.1,H0 y⟩
  have hx : f x' = x := Subtype.ext (chartCollarMap_outside_closed e hdpos 1
    (fun he => hxa ((image_mono (closedBall_subset_closedBall (min_le_left ..))) he)))
  have hy : f y' = y := Subtype.ext (chartCollarMap_outside_closed e hdpos 1
    (fun he => hyb ((image_mono (closedBall_subset_closedBall (min_le_right ..))) he)))
  exact ⟨((PathConnectedSpace.somePath x' y').map hc).cast hx.symm hy.symm⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.open_chart_core_path_connected
