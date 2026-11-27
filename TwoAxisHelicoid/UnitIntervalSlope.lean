import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue

namespace TwoAxisHelicoid
open Set

/-- A real motion whose speed is a fraction of the fixed speed b stays
on the segment from its starting point to that point plus b. -/
theorem unit_derivative_segment {u : ℝ → ℝ} {b : ℝ}
    (d : ∀ x∈Icc (0:ℝ) 1, ∃ k∈Icc (0:ℝ) 1, HasDerivAt u (k*b) x)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ∃ k∈Icc (0:ℝ) 1, u t=u 0+k*b := by
  by_cases z : t=0
  · exact ⟨0,⟨le_rfl,zero_le_one⟩,by simp [z]⟩
  have pos := lt_of_le_of_ne ht.1 (Ne.symm z)
  have diff (x : ℝ) (hx : x∈Icc 0 t) : DifferentiableAt ℝ u x := by
    obtain ⟨_,_,hd⟩ := d x ⟨hx.1,hx.2.trans ht.2⟩
    exact hd.differentiableAt
  obtain ⟨c,hc,slope⟩ := exists_deriv_eq_slope u pos
    (fun x hx => (diff x hx).continuousAt.continuousWithinAt)
    (fun x hx => (diff x (Ioo_subset_Icc_self hx)).differentiableWithinAt)
  obtain ⟨k,hk,dk⟩ := d c ⟨hc.1.le,hc.2.le.trans ht.2⟩
  rw [dk.deriv,sub_zero] at slope
  have h := (eq_div_iff z).mp slope
  exact ⟨t*k,⟨mul_nonneg ht.1 hk.1,(mul_le_mul_of_nonneg_right ht.2 hk.1).trans (by simpa using hk.2)⟩,by linarith only [h,show k*b*t=(t*k)*b by ring]⟩

/-- Integrating a constant vector derivative on the closed unit
interval recovers the actual vector displacement, including both endpoints. -/
theorem unit_constant_vector_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} {b : E} (d : ∀ t∈Icc (0:ℝ) 1, HasDerivAt F b t) :
    ∀ t∈Icc (0:ℝ) 1, F t=F 0+t • b := by
  let g := fun t : ℝ => F 0+t • b
  have dg (t : ℝ) : HasDerivAt g b t := by
    simpa only [id_eq,one_smul] using! ((hasDerivAt_id t).smul_const b).const_add (F 0)
  apply Convex.eqOn_of_fderivWithin_eq (𝕜 := ℝ) (convex_Icc (0:ℝ) 1)
    (fun t ht => (d t ht).differentiableAt.differentiableWithinAt)
    (fun t _ => (dg t).differentiableAt.differentiableWithinAt) (uniqueDiffOn_Icc zero_lt_one)
    _ (left_mem_Icc.mpr zero_le_one) (by simp [g])
  intro t ht
  exact ((d t ht).hasFDerivAt.hasFDerivWithinAt.fderivWithin (uniqueDiffOn_Icc zero_lt_one t ht)).trans
    ((dg t).hasFDerivAt.hasFDerivWithinAt.fderivWithin (uniqueDiffOn_Icc zero_lt_one t ht)).symm

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.unit_derivative_segment
#print axioms TwoAxisHelicoid.unit_constant_vector_derivative
