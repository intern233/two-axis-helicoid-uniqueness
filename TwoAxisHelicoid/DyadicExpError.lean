import TwoAxisHelicoid.DyadicBallScale
import TwoAxisHelicoid.ThetaDisk

namespace TwoAxisHelicoid.DyadicBall

def upper (b : DyadicBall) : ℤ := |b.re|+|b.im|+b.radius

theorem upper_toBall (prec : ℕ) (b : DyadicBall) :
    (b.toBall prec).center.absUpper+(b.toBall prec).radius =
      (b.upper : ℚ)/(denominator prec : ℚ) := by
  have hd : (0 : ℚ) < denominator prec := by exact_mod_cast denominator_pos prec
  unfold toBall QComplex.absUpper upper
  dsimp
  rw [abs_div, abs_div, abs_of_pos hd]
  push_cast
  ring

def ChecksExpGuard (prec n : ℕ) (b : DyadicBall) : Prop :=
  2*b.upper ≤ denominator prec*(n+1)

instance (prec n : ℕ) (b : DyadicBall) : Decidable (ChecksExpGuard prec n b) := by
  unfold ChecksExpGuard
  infer_instance

theorem checksExpGuard_sound {prec n : ℕ} {b : DyadicBall} (h : ChecksExpGuard prec n b) :
    ComplexBall.expGuard (b.toBall prec) n := by
  have hd : (0 : ℚ) < denominator prec := by exact_mod_cast denominator_pos prec
  have hh : 2*(b.upper : ℚ) ≤ (denominator prec : ℚ)*(n+1 : ℚ) := by exact_mod_cast h
  unfold ComplexBall.expGuard
  rw [upper_toBall]
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < n+1)).mpr
  apply (div_le_iff₀ hd).mpr
  linarith

def ChecksExpError (prec n : ℕ) (out sum input : DyadicBall) : Prop :=
  out.re = sum.re ∧ out.im = sum.im ∧ sum.radius ≤ out.radius ∧
    2*input.upper^n*denominator prec ≤
      ((out.radius : ℤ)-sum.radius)*(n.factorial : ℤ)*(denominator prec)^n

instance (prec n : ℕ) (out sum input : DyadicBall) : Decidable (ChecksExpError prec n out sum input) := by
  unfold ChecksExpError
  infer_instance

theorem checksExpError_coarsens {prec n : ℕ} {out sum input : DyadicBall}
    (h : ChecksExpError prec n out sum input) :
    (out.toBall prec).coarsens
      ((sum.toBall prec).inflate (ComplexBall.expError (input.toBall prec) n)) := by
  let D : ℚ := denominator prec
  have hd : 0 < D := by dsimp [D]; exact_mod_cast denominator_pos prec
  have hn : (0 : ℚ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hh : 2*(input.upper : ℚ)^n*D ≤
      ((out.radius : ℚ)-sum.radius)*(n.factorial : ℚ)*D^n := by
    dsimp [D]
    exact_mod_cast h.2.2.2
  have hdiv := div_le_div_of_nonneg_right hh (le_of_lt (mul_pos (mul_pos hd hn) (pow_pos hd n)))
  have he : ComplexBall.expError (input.toBall prec) n ≤
      ((out.radius : ℚ)-sum.radius)/D := by
    unfold ComplexBall.expError
    rw [upper_toBall]
    change ((input.upper : ℚ)/D)^n/(n.factorial : ℚ)*2 ≤ _
    rw [div_pow]
    convert hdiv using 1 <;> field_simp
  unfold ComplexBall.coarsens ComplexBall.inflate QComplex.sub QComplex.add QComplex.neg
    QComplex.absUpper toBall
  dsimp
  rw [h.1, h.2.1]
  simp only [add_neg_cancel, abs_zero, zero_add]
  change (sum.radius : ℚ)/D+ComplexBall.expError (input.toBall prec) n ≤ (out.radius : ℚ)/D
  have he' := he
  rw [sub_div] at he'
  linarith

end TwoAxisHelicoid.DyadicBall

#print axioms TwoAxisHelicoid.DyadicBall.checksExpError_coarsens
