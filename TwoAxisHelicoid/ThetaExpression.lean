import TwoAxisHelicoid.BallExpression
import TwoAxisHelicoid.ThetaTail

/-! Arithmetic expression trees denote the actual theta partial sums and tail majorants. -/

namespace TwoAxisHelicoid
namespace BallExpression

def imaginaryUnit : BallExpression := .const ⟨0, 1⟩

@[simp] theorem value_imaginaryUnit (env : ℕ → ℂ) : value env imaginaryUnit = Complex.I := by
  apply Complex.ext <;> simp [imaginaryUnit, value, QComplex.val]

def sineJetExpression (j : ℕ) (v : BallExpression) : BallExpression :=
  div (.mul (pow imaginaryUnit j)
    (sub (.exp (.mul v imaginaryUnit))
      (.mul (pow (rational (-1)) j) (.exp (.mul (.neg v) imaginaryUnit)))))
    (.mul (rational 2) imaginaryUnit)

@[simp] theorem value_sineJetExpression (env : ℕ → ℂ) (j : ℕ) (v : BallExpression) :
    value env (sineJetExpression j v) = sineJet j (value env v) := by
  simp [sineJetExpression, value, sineJet]

def thetaTermExpression (j n : ℕ) : BallExpression :=
  .mul (.mul (.mul (rational (if n%4<2 then 1 else -1))
    (.exp (.mul (.neg (.mul .pi (.input 0))) (rational ((n : ℚ)*(n+1)/2)))))
    (rational ((2*n+1 : ℚ)^j)))
    (sineJetExpression j (.mul (rational (2*n+1 : ℚ)) (.input 1)))

noncomputable def thetaValues (t : ℝ) (v : ℂ) : ℕ → ℂ
  | 0 => t
  | 1 => v
  | _+2 => 0

theorem value_thetaTermExpression (t : ℝ) (v : ℂ) (j n : ℕ) :
    value (thetaValues t v) (thetaTermExpression j n) = thetaTerm t j n v := by
  have he : Complex.exp (-((Real.pi : ℂ)*t)*((n : ℂ)*(n+1)/2)) =
      (Real.exp (-Real.pi*t*n*(n+1)/2) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  simp only [thetaTermExpression, value, value_rational, value_sineJetExpression,
    thetaValues, Rat.cast_pow, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one, he, thetaTerm]
  unfold thetaSign
  split_ifs <;> norm_num

def thetaPartialExpression (j : ℕ) : ℕ → BallExpression
  | 0 => rational 0
  | n+1 => .add (thetaPartialExpression j n) (thetaTermExpression j n)

theorem value_thetaPartialExpression (t : ℝ) (v : ℂ) (j N : ℕ) :
    value (thetaValues t v) (thetaPartialExpression j N) = thetaPartial t j N v := by
  induction N with
  | zero => simp [thetaPartialExpression, thetaPartial]
  | succ n ih =>
    simp only [thetaPartialExpression, value, value_thetaTermExpression, ih,
      thetaPartial, Finset.sum_range_succ]

def thetaMajorantExpression (tlo y : ℚ) (j N : ℕ) : BallExpression :=
  .mul (rational ((2*N+1 : ℚ)^j))
    (.exp (.add (.mul (.neg (.mul .pi (rational tlo)))
      (rational ((N : ℚ)*(N+1)/2))) (rational ((2*N+1 : ℚ)*y))))

def thetaRatioExpression (tlo y : ℚ) (j N : ℕ) : BallExpression :=
  .mul (rational (((2*N+3 : ℚ)/(2*N+1))^j))
    (.exp (.add (.mul (.neg (.mul .pi (rational tlo)))
      (rational (N+1 : ℚ))) (rational (2*y))))

theorem value_thetaMajorantExpression (env : ℕ → ℂ) (tlo y : ℚ) (j N : ℕ) :
    value env (thetaMajorantExpression tlo y j N) = (thetaMajorant tlo y j N : ℂ) := by
  simp only [thetaMajorantExpression, value, value_rational, thetaMajorant]
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  push_cast
  congr 1
  congr 1
  ring

theorem value_thetaRatioExpression (env : ℕ → ℂ) (tlo y : ℚ) (j N : ℕ) :
    value env (thetaRatioExpression tlo y j N) = (thetaRatio tlo y j N : ℂ) := by
  simp only [thetaRatioExpression, value, value_rational, thetaRatio]
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  push_cast
  congr 1
  congr 1
  ring

end BallExpression
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.BallExpression.value_thetaTermExpression
