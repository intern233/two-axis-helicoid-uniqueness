import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-! The normalized complex theta series in (8.1), defined without numerical oracles. -/

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

def thetaSign (n : ℕ) : ℂ := if n % 4 < 2 then 1 else -1

/-- An exponential formula for the j-th derivative of sine. -/
noncomputable def sineJet (j : ℕ) (z : ℂ) : ℂ :=
  I ^ j * (Complex.exp (z * I) - (-1 : ℂ) ^ j * Complex.exp (-z * I)) / (2 * I)

noncomputable def thetaTerm (t : ℝ) (j n : ℕ) (v : ℂ) : ℂ :=
  thetaSign n * (Real.exp (-Real.pi * t * n * (n + 1) / 2) : ℂ) *
    (2 * n + 1 : ℂ) ^ j * sineJet j ((2 * n + 1 : ℂ) * v)

noncomputable def thetaJet (t : ℝ) (j : ℕ) (v : ℂ) : ℂ :=
  ∑' n : ℕ, thetaTerm t j n v

noncomputable def thetaMajorant (t y : ℝ) (j n : ℕ) : ℝ :=
  (2 * n + 1 : ℝ) ^ j *
    Real.exp (-Real.pi * t * n * (n + 1) / 2 + (2 * n + 1) * y)

theorem thetaSign_norm (n : ℕ) : ‖thetaSign n‖ = 1 := by
  unfold thetaSign
  split <;> simp

theorem sineJet_zero (z : ℂ) : sineJet 0 z = Complex.sin z := by
  simp only [sineJet, pow_zero, one_mul, Complex.sin]
  field_simp
  simp [I_sq]

theorem sineJet_one (z : ℂ) : sineJet 1 z = Complex.cos z := by
  simp only [sineJet, pow_one, neg_one_mul, sub_neg_eq_add, Complex.cos]
  field_simp

theorem sineJet_norm_le (j : ℕ) (z : ℂ) :
    ‖sineJet j z‖ ≤ Real.exp |z.im| := by
  have h1 : ‖Complex.exp (z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using neg_le_abs z.im
  have h2 : ‖Complex.exp (-z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using le_abs_self z.im
  calc
    ‖sineJet j z‖ = ‖Complex.exp (z * I) - (-1 : ℂ)^j * Complex.exp (-z * I)‖ / 2 := by
      simp [sineJet, norm_pow]
    _ ≤ (‖Complex.exp (z * I)‖ + ‖(-1 : ℂ)^j * Complex.exp (-z * I)‖) / 2 := by
      exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
    _ ≤ Real.exp |z.im| := by
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      linarith

theorem thetaMajorant_nonneg (t y : ℝ) (j n : ℕ) : 0 ≤ thetaMajorant t y j n := by
  unfold thetaMajorant
  positivity

/-- Uniform domination simultaneously in the real parameter and complex argument. -/
theorem thetaTerm_norm_le {t tlo y : ℝ} (ht : tlo ≤ t) {v : ℂ}
    (hv : |v.im| ≤ y) (j n : ℕ) : ‖thetaTerm t j n v‖ ≤ thetaMajorant tlo y j n := by
  have hn : (0 : ℝ) ≤ 2 * n + 1 := by positivity
  have hk : (2 * n + 1 : ℂ) = ((2 * n + 1 : ℝ) : ℂ) := by push_cast; rfl
  have hv' : |((2 * n + 1 : ℂ) * v).im| ≤ (2 * n + 1 : ℝ) * y := by
    rw [hk]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [abs_mul, abs_of_nonneg hn]
    exact mul_le_mul_of_nonneg_left hv hn
  have he : -Real.pi * t * n * (n + 1) / 2 ≤ -Real.pi * tlo * n * (n + 1) / 2 := by
    have hprod : 0 ≤ Real.pi * (n : ℝ) * (n + 1) / 2 := by positivity
    nlinarith
  calc
    ‖thetaTerm t j n v‖ = Real.exp (-Real.pi * t * n * (n+1)/2) *
        (2 * n + 1 : ℝ)^j * ‖sineJet j ((2*n+1 : ℂ)*v)‖ := by
      simp only [thetaTerm, norm_mul, thetaSign_norm, norm_pow, one_mul, hk,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn,
        abs_of_nonneg (Real.exp_nonneg _)]
    _ ≤ Real.exp (-Real.pi * t * n * (n+1)/2) *
        (2 * n + 1 : ℝ)^j * Real.exp ((2*n+1)*y) := by
      apply mul_le_mul_of_nonneg_left
        ((sineJet_norm_le j _).trans (Real.exp_le_exp.mpr hv'))
      positivity
    _ ≤ thetaMajorant tlo y j n := by
      unfold thetaMajorant
      rw [Real.exp_add]
      have hh := Real.exp_le_exp.mpr he
      calc
        _ = Real.exp (-Real.pi * t * n * (n+1)/2) *
            ((2*n+1 : ℝ)^j * Real.exp ((2*n+1)*y)) := by ring
        _ ≤ Real.exp (-Real.pi * tlo * n * (n+1)/2) *
            ((2*n+1 : ℝ)^j * Real.exp ((2*n+1)*y)) :=
          mul_le_mul_of_nonneg_right hh (by positivity)
        _ = _ := by ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaTerm_norm_le
