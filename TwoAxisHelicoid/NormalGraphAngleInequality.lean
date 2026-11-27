module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

namespace TwoAxisHelicoid
open InnerProductSpace

/-- The acute angle between the base and graph tangent planes is computed
from their unit normals, with either choice of orientation. Here `A` acts
on the base tangent space and `du` is the differential of the graph height. -/
theorem normal_graph_tangent_angle_inequalities
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : Submodule ℝ E) (N n : E) (baseUnit : ‖N‖ = 1) (graphUnit : ‖n‖ = 1)
    (orthogonal : ∀ w : V, ⟪(w : E), N⟫_ℝ = 0)
    (transverse : ⟪N, n⟫_ℝ ≠ 0) (A : V →L[ℝ] V) (u : ℝ) (du : V →L[ℝ] ℝ)
    (graphTangent : ∀ v : V, ⟪((v - u • A v : V) : E) + du v • N, n⟫_ℝ = 0)
    (v : V) :
    let θ := Real.arccos |⟪N, n⟫_ℝ|
    |du v| ≤ Real.tan θ * ‖v - u • A v‖ ∧
      Real.tan θ * ‖v - u • A v‖ ≤ (1 + |u| * ‖A‖) * Real.tan θ * ‖v‖ := by
  let d := ⟪N, n⟫_ℝ
  let θ := Real.arccos |d|
  let w := v - u • A v
  have hd : 0 < |d| := abs_pos.mpr transverse
  have unitBound : |d| ≤ 1 := by simpa only [baseUnit,graphUnit,mul_one] using abs_real_inner_le_norm N n
  have cosθ : Real.cos θ = |d| := Real.cos_arccos (by linarith) unitBound
  have sinPos : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)
  have tanPos : 0 ≤ Real.tan θ := by
    rw [Real.tan_eq_sin_div_cos,cosθ]
    exact div_nonneg sinPos hd.le
  have normalComponent : ‖n - d • N‖ = Real.sin θ := by
    have diff := norm_sub_sq_real n (d • N)
    rw [norm_smul,Real.norm_eq_abs,baseUnit,mul_one,graphUnit,real_inner_smul_right,
      real_inner_comm N n] at diff
    change ‖n - d • N‖ ^ 2 = 1 ^ 2 - 2 * (d * d) + |d| ^ 2 at diff
    have trig := Real.sin_sq_add_cos_sq θ
    rw [cosθ,sq_abs] at trig
    rw [sq_abs] at diff
    exact (sq_eq_sq₀ (norm_nonneg _) sinPos).mp (by nlinarith only [diff,trig])
  have tangent := graphTangent v
  change ⟪(w : E) + du v • N, n⟫_ℝ = 0 at tangent
  rw [inner_add_left,real_inner_smul_left] at tangent
  change ⟪(w : E), n⟫_ℝ + du v * d = 0 at tangent
  have spatial : ⟪(w : E), n - d • N⟫_ℝ = -(du v * d) := by
    rw [inner_sub_right,real_inner_smul_right,orthogonal w,mul_zero,sub_zero]
    linarith only [tangent]
  have projected := abs_real_inner_le_norm (w : E) (n - d • N)
  rw [spatial,abs_neg,abs_mul,normalComponent] at projected
  change |du v| ≤ Real.tan θ * ‖w‖ ∧ Real.tan θ * ‖w‖ ≤ (1 + |u| * ‖A‖) * Real.tan θ * ‖v‖
  constructor
  · rw [Real.tan_eq_sin_div_cos,cosθ,div_mul_eq_mul_div]
    apply (le_div_iff₀ hd).mpr
    calc
      _ ≤ ‖(w : E)‖ * Real.sin θ := projected
      _ = Real.sin θ * ‖w‖ := by rw [Submodule.norm_coe, mul_comm]
  · have length : ‖w‖ ≤ (1 + |u| * ‖A‖) * ‖v‖ := calc
      ‖v - u • A v‖ ≤ ‖v‖ + ‖u • A v‖ := norm_sub_le _ _
      _ = ‖v‖ + |u| * ‖A v‖ := by rw [norm_smul,Real.norm_eq_abs]
      _ ≤ ‖v‖ + |u| * (‖A‖ * ‖v‖) := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (A.le_opNorm v) (abs_nonneg u))
      _ = (1 + |u| * ‖A‖) * ‖v‖ := by ring
    exact (mul_le_mul_of_nonneg_left length tanPos).trans_eq (by ring)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.normal_graph_tangent_angle_inequalities
