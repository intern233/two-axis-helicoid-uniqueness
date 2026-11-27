import TwoAxisHelicoid.LeftMomentEstimates

namespace TwoAxisHelicoid
open Set MeasureTheory

/-- Substitution ρ = exp(−πy) in the actual horizontal error moment
on an arbitrary oriented subinterval of the integration path. -/
theorem left_path_moment_subinterval {t : ℝ} (ht : 0 < t) (j : ℕ) (a b : ℝ) :
    (∫ y : ℝ in a..b, ‖leftComparisonFunction t (leftPathW y)‖ *
      (leftProductB t (Real.exp (-Real.pi*y)))^j) =
    (Real.pi/t) * ∫ x : ℝ in Real.exp (-Real.pi*b)..Real.exp (-Real.pi*a),
      leftMomentDensity (leftKappa t) x * (leftProductB t x)^j := by
  let f := fun y : ℝ => Real.exp (-Real.pi*y)
  let g := fun x : ℝ => leftMomentDensity (leftKappa t) x * (leftProductB t x)^j
  have hf (y : ℝ) : HasDerivAt f (-Real.pi*f y) y := by
    have h := ((hasDerivAt_id y).const_mul (-Real.pi)).exp
    convert h using 1
    · rfl
    · dsimp only [f, id_eq]
      ring
  have hg : ContinuousOn g (f '' uIcc a b) := by
    rintro x ⟨y, _, rfl⟩
    exact (leftMomentDensity_weight_continuousAt t j (Real.exp_ne_zero _)).continuousWithinAt
  have sub := intervalIntegral.integral_comp_mul_deriv' (a := a) (b := b)
    (f := f) (f' := fun y => -Real.pi*f y) (g := g)
    (fun y _ => hf y) (by dsimp [f]; fun_prop) hg
  change (∫ y : ℝ in a..b, g (f y)*(-Real.pi*f y)) = ∫ x : ℝ in f a..f b, g x at sub
  rw [intervalIntegral.integral_symm (a := f b) (b := f a)] at sub
  have factor : (fun y => g (f y)*(-Real.pi*f y)) = fun y =>
      (-t/Real.pi) * (‖leftComparisonFunction t (leftPathW y)‖ * (leftProductB t (f y))^j) := by
    funext y
    rw [leftComparison_norm ht]
    dsimp only [f, g]
    field_simp [ht.ne', Real.pi_ne_zero]
  rw [factor, intervalIntegral.integral_const_mul] at sub
  apply mul_left_cancel₀ (div_ne_zero (neg_ne_zero.mpr ht.ne') Real.pi_ne_zero : -t/Real.pi ≠ 0)
  calc
    _ = -(∫ x : ℝ in f b..f a, g x) := sub
    _ = (-t/Real.pi)*((Real.pi/t)*(∫ x : ℝ in f b..f a, g x)) := by
      field_simp [ht.ne', Real.pi_ne_zero]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.left_path_moment_subinterval
