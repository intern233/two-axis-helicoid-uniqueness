import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike

namespace TwoAxisHelicoid
open Set Metric
open scoped Topology NNReal

/-- A globally bounded smooth vector field in a proper normed space has an
actual solution on a neighborhood of the whole unit interval. -/
theorem bounded_smooth_vector_field_unit_solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ProperSpace E]
    {f : E → E} (hf : ContDiff ℝ 1 f) {L : ℝ} (hL : 0 ≤ L)
    (hb : ∀ x, ‖f x‖ ≤ L) (x₀ : E) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧ ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt γ (f (γ t)) t := by
  let a : ℝ≥0 := ⟨2*(L+1),by positivity⟩
  let l : ℝ≥0 := ⟨L,hL⟩
  obtain ⟨K,hK⟩ := hf.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall x₀ (a : ℝ)) (isCompact_closedBall x₀ (a : ℝ))
  have hp : IsPicardLindelof (fun _ : ℝ => f) (tmin := -1) (tmax := 2)
      ⟨0,by norm_num⟩ x₀ a 0 l K := by
    apply IsPicardLindelof.of_time_independent (fun x _ => hb x) hK
    change L*max ((2 : ℝ)-0) (0-(-1)) ≤ 2*(L+1)-0
    norm_num
    linarith
  obtain ⟨γ,hγ,hd⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨γ,hγ,?_⟩
  intro t ht
  have hi : t ∈ Ioo (-1 : ℝ) 2 := ⟨by linarith [ht.1],by linarith [ht.2]⟩
  exact (hd t (Ioo_subset_Icc_self hi)).hasDerivAt (Icc_mem_nhds hi.1 hi.2)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.bounded_smooth_vector_field_unit_solution
