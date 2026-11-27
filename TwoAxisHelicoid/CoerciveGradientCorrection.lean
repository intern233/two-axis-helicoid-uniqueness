module

public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

public section

namespace TwoAxisHelicoid
open InnerProductSpace
open scoped RealInnerProductSpace

/-- The weak Dirichlet correction in a closed subspace of gradients is
determined by its flux against every admissible test gradient. -/
theorem unique_coercive_gradient_correction {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (S : Submodule ℝ E) (hs : IsClosed (S : Set E))
    (T : E →L[ℝ] E) {c : ℝ} (hc : 0<c)
    (lower : ∀ v, c*‖v‖^2≤⟪T v,v⟫_ℝ) (e : E) :
    ∃! u : S, ∀ v : S, ⟪T (e+(u:E)),(v:E)⟫_ℝ=0 := by
  let : CompleteSpace S := hs.completeSpace_coe
  let inc := S.subtypeL
  let B : S →L[ℝ] S →L[ℝ] ℝ :=
    ((ContinuousLinearMap.compL ℝ S E ℝ).flip inc).comp ((innerSL ℝ).comp (T.comp inc))
  have coercive : IsCoercive B := by
    refine ⟨c,hc,fun v => ?_⟩
    change c*‖v‖*‖v‖≤⟪T (v:E),(v:E)⟫_ℝ
    simpa only [pow_two,mul_assoc,Submodule.norm_coe] using lower (v:E)
  let rhs : S →L[ℝ] ℝ := (innerSL ℝ (-(T e))).comp inc
  let f := (InnerProductSpace.toDual ℝ S).symm rhs
  have load (v : S) : ⟪f,v⟫_ℝ= -⟪T e,(v:E)⟫_ℝ := by
    change ⟪(InnerProductSpace.toDual ℝ S).symm rhs,v⟫_ℝ=_
    rw [InnerProductSpace.toDual_symm_apply]
    exact inner_neg_left _ _
  obtain ⟨u,hu⟩ := coercive.continuousLinearEquivOfBilin.surjective f
  refine ⟨u,?_,?_⟩
  · intro v
    have id := coercive.continuousLinearEquivOfBilin_apply u v
    rw [hu,load] at id
    change -⟪T e,(v:E)⟫_ℝ=⟪T (u:E),(v:E)⟫_ℝ at id
    rw [map_add,inner_add_left]
    linarith
  · intro w hw
    apply coercive.continuousLinearEquivOfBilin.injective
    rw [hu]
    symm
    apply coercive.unique_continuousLinearEquivOfBilin
    intro v
    rw [load]
    change -⟪T e,(v:E)⟫_ℝ=⟪T (w:E),(v:E)⟫_ℝ
    have eq := hw v
    rw [map_add,inner_add_left] at eq
    linarith

/-- Comparison with any constant-coefficient flux annihilating the test
space bounds the correction by the actual coefficient error. -/
theorem coercive_gradient_correction_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (S : Submodule ℝ E) (T : E →L[ℝ] E)
    {c : ℝ} (lower : ∀ v, c*‖v‖^2≤⟪T v,v⟫_ℝ) (e r : E)
    (orth : ∀ v : S, ⟪r,(v:E)⟫_ℝ=0) (u : S)
    (sol : ∀ v : S, ⟪T (e+(u:E)),(v:E)⟫_ℝ=0) : c*‖(u:E)‖ ≤ ‖r-T e‖ := by
  by_cases h : ‖(u:E)‖=0
  · rw [h,mul_zero]
    exact norm_nonneg _
  have pos := lt_of_le_of_ne (norm_nonneg (u:E)) (Ne.symm h)
  have id : ⟪T (u:E),(u:E)⟫_ℝ=⟪r-T e,(u:E)⟫_ℝ := by
    have eq := sol u
    rw [map_add,inner_add_left] at eq
    rw [inner_sub_left,orth u]
    linarith
  have estimate := (lower (u:E)).trans (id.le.trans (real_inner_le_norm _ _))
  apply (mul_le_mul_iff_left₀ pos).mp
  simpa only [pow_two,mul_assoc] using estimate
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.unique_coercive_gradient_correction
#print axioms TwoAxisHelicoid.coercive_gradient_correction_bound
