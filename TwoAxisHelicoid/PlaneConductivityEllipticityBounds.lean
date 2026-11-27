module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

public section
namespace TwoAxisHelicoid
open Complex Set Metric Topology
/-- A single constant bounds both sides of the energy form of a smooth,
compact perturbation of the identity, uniformly over all points and vectors. -/
theorem compact_plane_conductivity_uniform_bounds {A B C : ℂ → ℝ}
    (sa : Continuous A) (sc : Continuous C) (ha : ∀ z, 0<A z)
    (det : ∀ z, A z*C z-(B z)^2=1)
    {K : Set ℂ} (hk : IsCompact K) (off : ∀ z∉K, A z=1 ∧ B z=0 ∧ C z=1) :
    ∃ k : ℝ, 1≤k ∧ ∀ z x y,
      (x^2+y^2)/k ≤ C z*x^2-2*B z*x*y+A z*y^2 ∧
      C z*x^2-2*B z*x*y+A z*y^2 ≤ k*(x^2+y^2) := by
  obtain ⟨M,hm⟩ := hk.bddAbove_image (sa.add sc).continuousOn
  let k := max 2 M
  have two : (2:ℝ)≤k := le_max_left _ _
  have kp : 0<k := by linarith
  refine ⟨k,by linarith,?_⟩
  intro z x y
  let a := A z
  let b := B z
  let c := C z
  let Q := c*x^2-2*b*x*y+a*y^2
  have trace : a+c≤k := by
    by_cases hz : z∈K
    · exact (hm ⟨z,hz,rfl⟩).trans (le_max_right _ _)
    · obtain ⟨e,_,g⟩ := off z hz
      dsimp [a,c]
      rw [e,g]
      linarith
  have ac : a*c-b^2=1 := det z
  have ap : 0<a := ha z
  have qid : a*Q=(b*x-a*y)^2+x^2 := by
    dsimp only [Q]
    linear_combination x^2*ac
  have qpos : 0≤Q := by
    apply nonneg_of_mul_nonneg_right (a:=a)
    · rw [qid]
      positivity
    · exact ap
  have upper : Q≤(a+c)*(x^2+y^2) := by
    apply sub_nonneg.mp
    apply nonneg_of_mul_nonneg_right (a:=a)
    · have id : a*((a+c)*(x^2+y^2)-Q)=(a*x+b*y)^2+y^2 := by
        dsimp only [Q]
        linear_combination y^2*ac
      rw [id]
      positivity
    · exact ap
  have lower : x^2+y^2≤(a+c)*Q := by
    have id : (a+c)*Q-(x^2+y^2)=(c*x-b*y)^2+(b*x-a*y)^2 := by
      dsimp only [Q]
      linear_combination (x^2+y^2)*ac
    exact sub_nonneg.mp (id.symm ▸ add_nonneg (sq_nonneg _) (sq_nonneg _))
  constructor
  · apply (div_le_iff₀ kp).mpr
    rw [mul_comm Q k]
    exact lower.trans (mul_le_mul_of_nonneg_right trace qpos)
  · exact upper.trans (mul_le_mul_of_nonneg_right trace (by positivity))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_plane_conductivity_uniform_bounds
