import TwoAxisHelicoid.HelicoidGraphSmoothness
import TwoAxisHelicoid.ExteriorPlaneBase
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace TwoAxisHelicoid
open Set Filter Metric Bornology
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

theorem exterior_graph_height_uniform_bound {R : ℝ} {u : exteriorPlaneBase R → ℝ}
    (hu : Tendsto (fun p => |u p|)
      (comap (Subtype.val : exteriorPlaneBase R → ℝ × ℝ) (cobounded (ℝ × ℝ))) (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℝ, ∀ p : exteriorPlaneBase R, T ≤ ‖p.1‖ → |u p| < δ := by
  have hh := hu.eventually (gt_mem_nhds hδ)
  obtain ⟨S,hS,hsub⟩ := Filter.mem_comap.mp hh
  obtain ⟨T,_,hT⟩ := Filter.hasBasis_cobounded_norm.mem_iff.mp hS
  exact ⟨T,fun p hp => hsub (hT hp)⟩

/-- Cut off the actual smooth height on an exterior domain. The resulting
global smooth function vanishes near any prescribed bounded core, agrees
with the original height far out, and obeys any prescribed positive
uniform bound. -/
theorem exterior_graph_smooth_small_cutoff {R : ℝ} {u : exteriorPlaneBase R → ℝ}
    (hus : ContDiffOn ℝ (∞ : WithTop ℕ∞) (extendOpenScalar u) (exteriorPlaneBase R))
    (hu : Tendsto (fun p => |u p|)
      (comap (Subtype.val : exteriorPlaneBase R → ℝ × ℝ) (cobounded (ℝ × ℝ))) (𝓝 0))
    (A : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (v : ℝ × ℝ → ℝ) (B : ℝ), 0 < B ∧ R < B ∧ A < B ∧
      ContDiff ℝ (∞ : WithTop ℕ∞) v ∧ (∀ p, |v p| ≤ δ) ∧
      (∀ p, ‖p‖ ≤ B → v p = 0) ∧
      (∀ p : exteriorPlaneBase R, B+1 ≤ ‖p.1‖ → v p.1 = u p) := by
  obtain ⟨T,hT⟩ := exterior_graph_height_uniform_bound hu hδ
  obtain ⟨B,hB⟩ := exists_gt (max (max (max A R) T) 0)
  have hB0 : 0 < B := (le_max_right _ _).trans_lt hB
  have hBT : T < B := ((le_max_right (max A R) T).trans (le_max_left _ _)).trans_lt hB
  have hBR : R < B := (((le_max_right A R).trans (le_max_left _ _)).trans (le_max_left _ _)).trans_lt hB
  have hBA : A < B := (((le_max_left A R).trans (le_max_left _ _)).trans (le_max_left _ _)).trans_lt hB
  let χ : ContDiffBump (0 : ℝ × ℝ) := ⟨B,B+1,hB0,by linarith⟩
  let v : ℝ × ℝ → ℝ := fun p => (1-χ p)*extendOpenScalar u p
  have hz (p : ℝ × ℝ) (hp : ‖p‖ ≤ B) : χ p = 1 :=
    χ.one_of_mem_closedBall (by simpa only [mem_closedBall,dist_zero_right] using hp)
  have hvzero (p : ℝ × ℝ) (hp : ‖p‖ ≤ B) : v p = 0 := by
    simp only [v,hz p hp,sub_self,zero_mul]
  refine ⟨v,B,hB0,hBR,hBA,?_,?_,hvzero,?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p ∈ exteriorPlaneBase R
    · exact (contDiffAt_const.sub χ.contDiffAt).mul
        (hus.contDiffAt ((exteriorPlaneBase_isOpen R).mem_nhds hp))
    · have hn : ‖p‖ < B := (le_of_not_gt hp).trans_lt hBR
      have he : v =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
        filter_upwards [χ.eventuallyEq_one_of_mem_ball
          (by simpa only [mem_ball,dist_zero_right] using hn)] with q hq
        change χ q = 1 at hq
        simp only [v,hq,sub_self,zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  · intro p
    by_cases hp : ‖p‖ ≤ B
    · rw [hvzero p hp,abs_zero]
      exact hδ.le
    · have hpn : B < ‖p‖ := lt_of_not_ge hp
      have hpR : p ∈ exteriorPlaneBase R := hBR.trans hpn
      have hbound : |extendOpenScalar u p| ≤ δ := by
        simpa only [extendOpenScalar,dite_eq_left hpR] using (hT ⟨p,hpR⟩ (hBT.trans hpn).le).le
      have hχ : |1-χ p| ≤ 1 := by
        rw [abs_of_nonneg (sub_nonneg.mpr χ.le_one)]
        linarith [χ.nonneg (x := p)]
      change |(1-χ p)*extendOpenScalar u p| ≤ δ
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hχ (abs_nonneg _)).trans (by simpa only [one_mul] using hbound)
  · intro p hp
    have hχ : χ p.1 = 0 := χ.zero_of_le_dist (by simpa only [dist_zero_right] using hp)
    simp only [v,hχ,sub_zero,one_mul,extendOpenScalar,dite_eq_left p.2]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.exterior_graph_smooth_small_cutoff
