import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Set Filter Metric Complex
open scoped Topology

/-- A vector primitive of a derivative negligible relative to the
derivative of an increasing divergent real envelope is negligible
relative to the envelope itself. This also applies to a complex
primitive with rapidly rotating argument. -/
theorem growing_primitive_negligible {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F D : ℝ → E} {R V : ℝ → ℝ} (escape : Tendsto R atTop atTop)
    (regular : ∀ᶠ t in atTop, HasDerivAt F (D t) t ∧ HasDerivAt R (V t) t ∧ 0<V t)
    (small : Tendsto (fun t => ‖D t‖/V t) atTop (𝓝 0)) :
    Tendsto (fun t => ‖F t‖/R t) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  let δ := ε/2
  have dp : 0<δ := half_pos ep
  obtain ⟨a,tail⟩ := eventually_atTop.mp (regular.and (small.eventually (gt_mem_nhds dp)))
  let B := fun t => ‖F a‖+δ*(R t-R a)
  have bD (t : ℝ) (ht : a≤t) : HasDerivAt B (δ*V t) t := (((tail t ht).1.2.1.sub_const (R a)).const_mul δ).const_add ‖F a‖
  have bound (b : ℝ) (hb : a≤b) : ‖F b‖≤B b := by
    apply image_norm_le_of_norm_deriv_right_le_deriv_boundary' (a := a) (b := b)
      (fun t ht => (tail t ht.1).1.1.continuousAt.continuousWithinAt)
      (fun t ht => (tail t ht.1).1.1.hasDerivWithinAt)
      (show ‖F a‖≤B a by simp [B]) (fun t ht => (bD t ht.1).continuousAt.continuousWithinAt)
      (fun t ht => (bD t ht.1).hasDerivWithinAt) (fun t ht => ?_) ⟨hb,le_rfl⟩
    exact ((div_lt_iff₀ (tail t ht.1).1.2.2).mp (tail t ht.1).2).le
  let C := ‖F a‖-δ*R a
  have negligible : Tendsto (fun t => C/R t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Pi.inv_apply] using (tendsto_const_nhds (x := C)).mul escape.inv_tendsto_atTop
  filter_upwards [eventually_ge_atTop a,escape.eventually_gt_atTop 0,negligible.eventually (gt_mem_nhds dp)] with t ht pos c
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (norm_nonneg _) pos.le)]
  have e : ‖F t‖/R t≤C/R t+δ := by
    apply (div_le_iff₀ pos).mpr
    rw [add_mul,div_mul_cancel₀ _ pos.ne']
    simpa only [B,C] using (bound t ht).trans_eq (by dsimp [B,C]; ring)
  dsimp [δ] at c e
  linarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.growing_primitive_negligible
