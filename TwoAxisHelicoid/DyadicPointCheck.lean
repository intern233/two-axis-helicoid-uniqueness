import TwoAxisHelicoid.DyadicBallBasic

namespace TwoAxisHelicoid.DyadicBall

/-- Integer-only comparison with a rational complex point. -/
def ChecksPoint (prec : ℕ) (out : DyadicBall) (c : QComplex) : Prop :=
  |out.re*(c.re.den : ℤ)-c.re.num*denominator prec| *(c.im.den : ℤ)+
    |out.im*(c.im.den : ℤ)-c.im.num*denominator prec| *(c.re.den : ℤ) ≤
      (out.radius : ℤ)*c.re.den*c.im.den

instance (prec : ℕ) (out : DyadicBall) (c : QComplex) : Decidable (ChecksPoint prec out c) := by
  unfold ChecksPoint
  infer_instance

theorem checksPoint_iff (prec : ℕ) (out : DyadicBall) (c : QComplex) :
    ChecksPoint prec out c ↔ (out.toBall prec).coarsens (ComplexBall.point c) := by
  let D : ℚ := denominator prec
  let dr : ℚ := c.re.den
  let di : ℚ := c.im.den
  have hd : 0 < D := by dsimp [D]; exact_mod_cast denominator_pos prec
  have hdr : 0 < dr := by dsimp [dr]; exact_mod_cast c.re.den_pos
  have hdi : 0 < di := by dsimp [di]; exact_mod_cast c.im.den_pos
  have hr : c.re+ -((out.re : ℚ)/D) = -((out.re : ℚ)*dr-c.re.num*D)/(D*dr) := by
    calc
      _ = (c.re.num : ℚ)/dr+ -((out.re : ℚ)/D) := by rw [Rat.num_div_den]
      _ = _ := by field_simp; ring
  have hi : c.im+ -((out.im : ℚ)/D) = -((out.im : ℚ)*di-c.im.num*D)/(D*di) := by
    calc
      _ = (c.im.num : ℚ)/di+ -((out.im : ℚ)/D) := by rw [Rat.num_div_den]
      _ = _ := by field_simp; ring
  have he : |(out.re : ℚ)*dr-c.re.num*D|/(D*dr)+
      |(out.im : ℚ)*di-c.im.num*D|/(D*di) =
      (|(out.re : ℚ)*dr-c.re.num*D| *di+|(out.im : ℚ)*di-c.im.num*D| *dr)/(D*dr*di) := by
    field_simp
  unfold ComplexBall.coarsens ComplexBall.point QComplex.sub QComplex.add QComplex.neg
    QComplex.absUpper toBall
  dsimp
  change ChecksPoint prec out c ↔
    |c.re+ -((out.re : ℚ)/D)|+|c.im+ -((out.im : ℚ)/D)|+0 ≤ (out.radius : ℚ)/D
  rw [hr, hi, abs_div, abs_div, abs_neg, abs_neg,
    abs_of_pos (mul_pos hd hdr), abs_of_pos (mul_pos hd hdi), add_zero, he]
  rw [div_le_div_iff₀ (mul_pos (mul_pos hd hdr) hdi) hd]
  have heq : (out.radius : ℚ)*(D*dr*di) = ((out.radius : ℚ)*dr*di)*D := by ring
  rw [heq, mul_le_mul_iff_left₀ hd]
  unfold ChecksPoint
  dsimp [dr, di, D]
  exact_mod_cast Iff.rfl

end TwoAxisHelicoid.DyadicBall

#print axioms TwoAxisHelicoid.DyadicBall.checksPoint_iff
