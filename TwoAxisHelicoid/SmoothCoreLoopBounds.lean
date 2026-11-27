import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Topology.MetricSpace.Pseudo.Basic

namespace TwoAxisHelicoid
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace

/-- The length bound needed when a compact core is carried into a smoothly
converging sequence of Euclidean surfaces. Only uniform convergence of
velocities on the unit parameter interval and a continuous limiting
velocity enter this estimate. -/
theorem bounded_lengths_of_uniformly_convergent_core_velocities
    {P : ℕ → ℝ → EuclideanSpace ℝ (Fin 3)} {v : ℝ → EuclideanSpace ℝ (Fin 3)}
    (hv : ContinuousOn v (Icc 0 1))
    (hc : TendstoUniformlyOn (fun n s => deriv (P n) s) v atTop (Icc 0 1)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop,
      Manifold.pathELength 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (P n) 0 1 ≤ ENNReal.ofReal B := by
  obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image hv.norm
  let B := max M 0+1
  refine ⟨B,by dsimp [B]; positivity,?_⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hc) 1 zero_lt_one] with n hn
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  calc
    _ ≤ ∫⁻ _ in Icc (0:ℝ) 1, ENNReal.ofReal B := by
      apply setLIntegral_mono' measurableSet_Icc
      intro s hs
      rw [mfderiv_eq_fderiv]
      change ‖deriv (P n) s‖ₑ ≤ ENNReal.ofReal B
      rw [← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      have he := hn s hs
      have hm : ‖v s‖ ≤ M := hM (mem_image_of_mem _ hs)
      have ht := dist_triangle (deriv (P n) s) (v s) 0
      rw [dist_zero_right,dist_zero_right,dist_comm (deriv (P n) s)] at ht
      dsimp [B]
      linarith [le_max_left M 0]
    _ = _ := by simp [Real.volume_Icc]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.bounded_lengths_of_uniformly_convergent_core_velocities
