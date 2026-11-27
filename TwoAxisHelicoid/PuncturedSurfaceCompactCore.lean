import TwoAxisHelicoid.PuncturedChartCollar

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology
open scoped Topology

/-- A compact surface with one puncture strongly deformation retracts onto
a compact core. Both the core and its retraction are obtained from any
actual complex chart at the puncture. -/
theorem punctured_surface_has_compact_core_retraction {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] (e : OpenPartialHomeomorph M ℂ) {p : M} (hp : p ∈ e.source) :
    ∃ (K : Set {x : M // x ≠ p}) (H : C(unitInterval × {x : M // x ≠ p},{x : M // x ≠ p})),
      IsCompact K ∧ (∀ x, H (0,x) = x) ∧ (∀ x, H (1,x) ∈ K) ∧
      ∀ s x, x ∈ K → H (s,x) = x := by
  classical
  obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source hp))
  let r := R/2
  have hr : 0 < r := half_pos hR
  have hB : closedBall (e p) r ⊆ e.target := (closedBall_subset_ball (half_lt_self hR)).trans hsub
  let U := e.symm '' ball (e p) r
  have hU : IsOpen U := e.isOpen_image_symm_of_subset_target isOpen_ball (ball_subset_closedBall.trans hB)
  have hpU : p ∈ U := ⟨e p,mem_ball_self hr,e.left_inv hp⟩
  let K := {x : {x : M // x ≠ p} | x.1 ∉ U}
  have hK : IsCompact K := by
    apply IsEmbedding.subtypeVal.isCompact_iff.mpr
    have heq : Subtype.val '' K = Uᶜ := by
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩
        exact hz
      · intro hz
        exact ⟨⟨y,fun he => hz (he ▸ hpU)⟩,hz,rfl⟩
    rw [heq]
    exact hU.isClosed_compl.isCompact
  let H : C(unitInterval × {x : M // x ≠ p},{x : M // x ≠ p}) :=
    ⟨fun u => ⟨chartCollarMap e p r u.1 u.2.1,chartCollarMap_nonpuncture e hp hr hB u.1 u.2.2⟩,
      (chartCollarMap_joint_continuous e hp hr hB).subtype_mk _⟩
  refine ⟨K,H,hK,?_,?_,?_⟩
  · intro x
    apply Subtype.ext
    by_cases hs : x.1 ∈ e.source
    · have hn : e x.1 ≠ e p := fun h => x.2 (e.injOn hs hp h)
      simp [H,chartCollarMap,hs,chartCollarPoint_fixed hn (show (0:ℝ)*r ≤ ‖e x.1-e p‖ by simp),e.left_inv hs]
    · simp [H,chartCollarMap,hs]
  · intro x
    change chartCollarMap e p r 1 x.1 ∉ U
    rintro ⟨w,hw,he⟩
    have hwT := hB (ball_subset_closedBall hw)
    by_cases hs : x.1 ∈ e.source
    · have hn : e x.1 ≠ e p := fun h => x.2 (e.injOn hs hp h)
      have ht := chartCollarPoint_target hr hn (e.map_source hs) hB (1:unitInterval)
      have heq := congrArg e he
      simp only [chartCollarMap,hs,ite_true,e.right_inv hwT,e.right_inv ht] at heq
      change w = chartCollarPoint (e p) r (1 : ℝ) (e x.1) at heq
      have hlt := (show max ‖e x.1-e p‖ ((1:ℝ)*r) < r by
        rw [← chartCollarPoint_dist hn,← heq]; exact hw)
      simpa only [one_mul,lt_self_iff_false,and_false] using max_lt_iff.mp hlt
    · simp only [chartCollarMap,hs,ite_false] at he
      exact hs (he ▸ e.map_target hwT)
  · intro s x hx
    apply Subtype.ext
    by_cases hs : x.1 ∈ e.source
    · have hn : e x.1 ≠ e p := fun h => x.2 (e.injOn hs hp h)
      have hfar : r ≤ ‖e x.1-e p‖ := le_of_not_gt (fun hl => hx ⟨e x.1,by rwa [mem_ball,dist_eq_norm],e.left_inv hs⟩)
      have hsr : s.1*r ≤ r := by simpa only [one_mul] using mul_le_mul_of_nonneg_right s.2.2 hr.le
      simp only [H,ContinuousMap.coe_mk,chartCollarMap,hs,ite_true,chartCollarPoint_fixed hn (hsr.trans hfar),e.left_inv hs]
    · simp [H,chartCollarMap,hs]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.punctured_surface_has_compact_core_retraction
