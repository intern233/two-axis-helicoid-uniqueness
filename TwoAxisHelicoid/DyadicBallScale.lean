import TwoAxisHelicoid.DyadicBall
import TwoAxisHelicoid.ComplexBallExp

namespace TwoAxisHelicoid.DyadicBall

def ChecksDivNat (out a : DyadicBall) (m : ℕ) : Prop :=
  0 < m ∧ |out.re*m-a.re|+|out.im*m-a.im|+(a.radius : ℤ) ≤ (out.radius : ℤ)*m

instance (out a : DyadicBall) (m : ℕ) : Decidable (ChecksDivNat out a m) := by
  unfold ChecksDivNat
  infer_instance

theorem checksDivNat_coarsens (prec : ℕ) {out a : DyadicBall} {m : ℕ}
    (h : ChecksDivNat out a m) :
    (out.toBall prec).coarsens (ComplexBall.scale (1/(m : ℚ)) (a.toBall prec)) := by
  let D : ℚ := denominator prec
  have hd : 0 < D := by dsimp [D]; exact_mod_cast denominator_pos prec
  have hm : (0 : ℚ) < m := by exact_mod_cast h.1
  have hh : |(out.re : ℚ)*m-a.re|+|(out.im : ℚ)*m-a.im|+(a.radius : ℚ) ≤
      (out.radius : ℚ)*m := by exact_mod_cast h.2
  unfold ComplexBall.coarsens ComplexBall.scale ComplexBall.mul ComplexBall.rational
    ComplexBall.point QComplex.ofRat QComplex.sub QComplex.add QComplex.neg QComplex.mul
    QComplex.absUpper toBall
  dsimp
  change |1/(m : ℚ)*((a.re : ℚ)/D)-0*((a.im : ℚ)/D)+-((out.re : ℚ)/D)|+
    |1/(m : ℚ)*((a.im : ℚ)/D)+0*((a.re : ℚ)/D)+-((out.im : ℚ)/D)|+
    ((|1/(m : ℚ)|+|0|)*((a.radius : ℚ)/D)+
      (|(a.re : ℚ)/D|+|(a.im : ℚ)/D|)*0+0*((a.radius : ℚ)/D)) ≤ (out.radius : ℚ)/D
  simp only [zero_mul, add_zero, sub_zero, mul_zero, abs_zero, abs_of_pos (one_div_pos.mpr hm)]
  have h1 : 1/(m : ℚ)*((a.re : ℚ)/D)+-((out.re : ℚ)/D) =
      -((out.re : ℚ)*m-a.re)/(m*D) := by field_simp; ring
  have h2 : 1/(m : ℚ)*((a.im : ℚ)/D)+-((out.im : ℚ)/D) =
      -((out.im : ℚ)*m-a.im)/(m*D) := by field_simp; ring
  rw [h1, h2, abs_div, abs_div, abs_neg, abs_neg, abs_of_pos (mul_pos hm hd)]
  calc
    _ = (|(out.re : ℚ)*m-a.re|+|(out.im : ℚ)*m-a.im|+(a.radius : ℚ))/(m*D) := by ring
    _ ≤ ((out.radius : ℚ)*m)/(m*D) := div_le_div_of_nonneg_right hh (by positivity)
    _ = _ := by field_simp

theorem divNat_contains {prec : ℕ} {out a : DyadicBall} {z : ℂ} {m : ℕ}
    (ha : (a.toBall prec).Contains z) (h : ChecksDivNat out a m) :
    (out.toBall prec).Contains (z/(m : ℂ)) := by
  have hb := ComplexBall.coarsen_contains (ComplexBall.scale_contains ha (1/(m : ℚ)))
    (checksDivNat_coarsens prec h)
  convert hb using 1
  push_cast
  ring

end TwoAxisHelicoid.DyadicBall

#print axioms TwoAxisHelicoid.DyadicBall.divNat_contains
