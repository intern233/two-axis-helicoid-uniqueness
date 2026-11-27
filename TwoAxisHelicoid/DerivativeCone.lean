import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace TwoAxisHelicoid
open Set

/-- A derivative constrained to a closed planar cone has every oriented
secant in the same cone. This uses the real mean value theorem. -/
theorem derivative_cone_secant_bound {r t r' t' : ℝ → ℝ} {a b κ : ℝ} (hab : a ≤ b)
    (hr : ∀ s ∈ Icc a b, HasDerivAt r (r' s) s)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (t' s) s)
    (hcone : ∀ s ∈ Icc a b, |t' s| ≤ κ*r' s) :
    |t b-t a| ≤ κ*(r b-r a) := by
  have hm s (hs : s ∈ Icc a b) := ((hr s hs).const_mul κ).sub (ht s hs)
  have hp s (hs : s ∈ Icc a b) := ((hr s hs).const_mul κ).add (ht s hs)
  have hmonoM := monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (fun s hs => (hm s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hm s (interior_subset hs)).differentiableAt.differentiableWithinAt)
    (fun s hs => by
      rw [(hm s (interior_subset hs)).deriv]
      have hh := (abs_le.mp (hcone s (interior_subset hs))).2
      linarith)
  have hmonoP := monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (fun s hs => (hp s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hp s (interior_subset hs)).differentiableAt.differentiableWithinAt)
    (fun s hs => by
      rw [(hp s (interior_subset hs)).deriv]
      have hh := (abs_le.mp (hcone s (interior_subset hs))).1
      linarith)
  have hM := hmonoM (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  have hP := hmonoP (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  simp only [Pi.sub_apply,Pi.add_apply] at hM hP
  apply abs_le.mpr
  constructor <;> nlinarith only [hM,hP]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.derivative_cone_secant_bound
