module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Matrix.Mul

public section

namespace TwoAxisHelicoid
open Complex Matrix

private theorem chart_directional_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → E} {z : ℂ} (df : DifferentiableAt ℝ f z) (v : ℂ) :
    HasDerivAt (fun r : ℝ => f (z + (r : ℂ) * v)) (fderiv ℝ f z v) 0 := by
  have line : HasDerivAt (fun r : ℝ => z + (r : ℂ) * v) v 0 := by
    have h := ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_id (0 : ℝ))).mul_const v).const_add z
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul, Function.comp_def, id_eq] using h
  have h : HasFDerivAt f (fderiv ℝ f z) (z + ((0 : ℝ) : ℂ) * v) := by simpa using df.hasFDerivAt
  exact h.comp_hasDerivAt 0 line

/-- The actual tangent to a spatial normal displacement in any chart direction. -/
theorem displaced_chart_tangent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Y N : ℂ → E} {u : ℂ → ℝ} {z : ℂ} (dY : DifferentiableAt ℝ Y z)
    (du : DifferentiableAt ℝ u z) (dN : DifferentiableAt ℝ N z) (s : ℝ) (v : ℂ) :
    deriv (fun r : ℝ => let w := z + (r : ℂ) * v; Y w + s • (u w • N w)) 0 =
      fderiv ℝ Y z v + s • (fderiv ℝ u z v • N z + u z • fderiv ℝ N z v) := by
  let w := fun r : ℝ => z + (r : ℂ) * v
  have functions : (fun r => Y (w r) + s • (u (w r) • N (w r))) =
      (fun r => Y (w r)) + s • ((fun r => u (w r)) • (fun r => N (w r))) := by
    funext r
    simp only [Pi.add_apply, Pi.smul_apply, Pi.smul_apply']
  change deriv (fun r => Y (w r) + s • (u (w r) • N (w r))) 0 = _
  rw [functions]
  simpa only [w, Complex.ofReal_zero, zero_mul, add_zero, add_comm (u z • fderiv ℝ N z v)] using
    ((chart_directional_derivative dY v).add (((chart_directional_derivative du v).smul
      (chart_directional_derivative dN v)).const_smul s)).deriv

/-- The Gram area of the two derivatives of the displaced surface agrees for
every displacement parameter with the Gram area of its explicit tangent vectors. -/
theorem displaced_chart_gram_area {Y N : ℂ → Fin 3 → ℝ} {u : ℂ → ℝ} {z : ℂ}
    (dY : DifferentiableAt ℝ Y z) (du : DifferentiableAt ℝ u z) (dN : DifferentiableAt ℝ N z) :
    (fun s : ℝ =>
      let Z := fun w => Y w + s • (u w • N w)
      let A := deriv (fun r : ℝ => Z (z + (r : ℂ))) 0
      let B := deriv (fun r : ℝ => Z (z + I * (r : ℂ))) 0
      Real.sqrt ((A ⬝ᵥ A) * (B ⬝ᵥ B) - (A ⬝ᵥ B)^2)) =
    (fun s : ℝ =>
      let T := fun v : ℂ => fderiv ℝ Y z v + s • (fderiv ℝ u z v • N z + u z • fderiv ℝ N z v)
      Real.sqrt ((T 1 ⬝ᵥ T 1) * (T I ⬝ᵥ T I) - (T 1 ⬝ᵥ T I)^2)) := by
  funext s
  let Z := fun w => Y w + s • (u w • N w)
  let T := fun v : ℂ => fderiv ℝ Y z v + s • (fderiv ℝ u z v • N z + u z • fderiv ℝ N z v)
  have dx : deriv (fun r : ℝ => Z (z + (r : ℂ))) 0 = T 1 := by
    simpa only [Z, T, mul_one] using displaced_chart_tangent dY du dN s 1
  have dy : deriv (fun r : ℝ => Z (z + I * (r : ℂ))) 0 = T I := by
    have same : (fun r : ℝ => Z (z + I * (r : ℂ))) = (fun r : ℝ => Z (z + (r : ℂ) * I)) := by
      funext r
      rw [mul_comm I]
    rw [same]
    exact displaced_chart_tangent dY du dN s I
  let A := deriv (fun r : ℝ => Z (z + (r : ℂ))) 0
  let B := deriv (fun r : ℝ => Z (z + I * (r : ℂ))) 0
  change Real.sqrt ((A ⬝ᵥ A) * (B ⬝ᵥ B) - (A ⬝ᵥ B)^2) =
    Real.sqrt ((T 1 ⬝ᵥ T 1) * (T I ⬝ᵥ T I) - (T 1 ⬝ᵥ T I)^2)
  rw [show A = T 1 from dx, show B = T I from dy]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.displaced_chart_tangent
#print axioms TwoAxisHelicoid.displaced_chart_gram_area
