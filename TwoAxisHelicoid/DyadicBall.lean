import TwoAxisHelicoid.ComplexBall

namespace TwoAxisHelicoid

/-- A disk whose three coordinates share a fixed dyadic denominator. -/
structure DyadicBall where
  re : ℤ
  im : ℤ
  radius : ℕ
  deriving DecidableEq, Repr

namespace DyadicBall

def denominator (prec : ℕ) : ℤ := 2^prec

def toBall (prec : ℕ) (b : DyadicBall) : ComplexBall :=
  ⟨⟨(b.re : ℚ)/(denominator prec : ℚ), (b.im : ℚ)/(denominator prec : ℚ)⟩,
    (b.radius : ℚ)/(denominator prec : ℚ)⟩

theorem denominator_pos (prec : ℕ) : 0 < denominator prec := by
  unfold denominator
  positivity

def ChecksAdd (out a b : DyadicBall) : Prop :=
  |out.re-(a.re+b.re)|+|out.im-(a.im+b.im)|+(a.radius : ℤ)+b.radius ≤ out.radius

instance (out a b : DyadicBall) : Decidable (ChecksAdd out a b) := by
  unfold ChecksAdd
  infer_instance

theorem checksAdd_coarsens (prec : ℕ) {out a b : DyadicBall} (h : ChecksAdd out a b) :
    (out.toBall prec).coarsens (ComplexBall.add (a.toBall prec) (b.toBall prec)) := by
  have hd : (0 : ℚ) < denominator prec := by exact_mod_cast denominator_pos prec
  have hh : |(out.re : ℚ)-((a.re : ℚ)+b.re)|+|(out.im : ℚ)-((a.im : ℚ)+b.im)|+
      (a.radius : ℚ)+b.radius ≤ out.radius := by exact_mod_cast h
  unfold ComplexBall.coarsens ComplexBall.add QComplex.sub QComplex.add QComplex.neg
    QComplex.absUpper toBall
  dsimp
  have h1 : (a.re : ℚ)/denominator prec+b.re/denominator prec+-(out.re/denominator prec) =
      -((out.re : ℚ)-((a.re : ℚ)+b.re))/denominator prec := by ring
  have h2 : (a.im : ℚ)/denominator prec+b.im/denominator prec+-(out.im/denominator prec) =
      -((out.im : ℚ)-((a.im : ℚ)+b.im))/denominator prec := by ring
  rw [h1, h2, abs_div, abs_div, abs_neg, abs_neg, abs_of_pos hd]
  convert (div_le_div_of_nonneg_right hh hd.le) using 1
  ring

def ChecksMul (prec : ℕ) (out a b : DyadicBall) : Prop :=
  |out.re*denominator prec-(a.re*b.re-a.im*b.im)|+
    |out.im*denominator prec-(a.re*b.im+a.im*b.re)|+
    (|a.re|+|a.im|)*(b.radius : ℤ)+(|b.re|+|b.im|)*(a.radius : ℤ)+
      (a.radius : ℤ)*b.radius ≤ (out.radius : ℤ)*denominator prec

instance (prec : ℕ) (out a b : DyadicBall) : Decidable (ChecksMul prec out a b) := by
  unfold ChecksMul
  infer_instance

theorem checksMul_coarsens (prec : ℕ) {out a b : DyadicBall} (h : ChecksMul prec out a b) :
    (out.toBall prec).coarsens (ComplexBall.mul (a.toBall prec) (b.toBall prec)) := by
  let D : ℚ := denominator prec
  have hd : 0 < D := by dsimp [D]; exact_mod_cast denominator_pos prec
  have hh : |(out.re : ℚ)*D-((a.re : ℚ)*b.re-(a.im : ℚ)*b.im)|+
      |(out.im : ℚ)*D-((a.re : ℚ)*b.im+(a.im : ℚ)*b.re)|+
      (|(a.re : ℚ)|+|(a.im : ℚ)|)*(b.radius : ℚ)+
      (|(b.re : ℚ)|+|(b.im : ℚ)|)*(a.radius : ℚ)+
      (a.radius : ℚ)*b.radius ≤ (out.radius : ℚ)*D := by
    dsimp [D]
    exact_mod_cast h
  unfold ComplexBall.coarsens ComplexBall.mul QComplex.sub QComplex.add QComplex.neg
    QComplex.mul QComplex.absUpper toBall
  dsimp
  change |((a.re : ℚ)/D*(b.re/D)-(a.im/D)*(b.im/D))+-(out.re/D)|+
    |((a.re : ℚ)/D*(b.im/D)+(a.im/D)*(b.re/D))+-(out.im/D)|+
    ((|(a.re : ℚ)/D|+|(a.im : ℚ)/D|)*(b.radius/D)+
      (|(b.re : ℚ)/D|+|(b.im : ℚ)/D|)*(a.radius/D)+(a.radius : ℚ)/D*(b.radius/D)) ≤ out.radius/D
  have h1 : ((a.re : ℚ)/D*(b.re/D)-(a.im/D)*(b.im/D))+-(out.re/D) =
      -((out.re : ℚ)*D-((a.re : ℚ)*b.re-(a.im : ℚ)*b.im))/D^2 := by field_simp; ring
  have h2 : ((a.re : ℚ)/D*(b.im/D)+(a.im/D)*(b.re/D))+-(out.im/D) =
      -((out.im : ℚ)*D-((a.re : ℚ)*b.im+(a.im : ℚ)*b.re))/D^2 := by field_simp; ring
  rw [h1, h2]
  simp only [abs_div, abs_neg, abs_of_pos hd, abs_of_pos (pow_pos hd 2)]
  have he : |(out.re : ℚ)*D-((a.re : ℚ)*b.re-(a.im : ℚ)*b.im)|/D^2+
      |(out.im : ℚ)*D-((a.re : ℚ)*b.im+(a.im : ℚ)*b.re)|/D^2+
      ((|(a.re : ℚ)|/D+|(a.im : ℚ)|/D)*(b.radius/D)+
      (|(b.re : ℚ)|/D+|(b.im : ℚ)|/D)*(a.radius/D)+(a.radius : ℚ)/D*(b.radius/D)) =
      (|(out.re : ℚ)*D-((a.re : ℚ)*b.re-(a.im : ℚ)*b.im)|+
      |(out.im : ℚ)*D-((a.re : ℚ)*b.im+(a.im : ℚ)*b.re)|+
      (|(a.re : ℚ)|+|(a.im : ℚ)|)*(b.radius : ℚ)+
      (|(b.re : ℚ)|+|(b.im : ℚ)|)*(a.radius : ℚ)+(a.radius : ℚ)*b.radius)/D^2 := by ring
  rw [he]
  calc
    _ ≤ ((out.radius : ℚ)*D)/D^2 := div_le_div_of_nonneg_right hh (by positivity)
    _ = _ := by field_simp

theorem add_contains {prec : ℕ} {out a b : DyadicBall} {z w : ℂ}
    (ha : (a.toBall prec).Contains z) (hb : (b.toBall prec).Contains w)
    (h : ChecksAdd out a b) : (out.toBall prec).Contains (z+w) :=
  ComplexBall.coarsen_contains (ComplexBall.add_contains ha hb) (checksAdd_coarsens prec h)

theorem mul_contains {prec : ℕ} {out a b : DyadicBall} {z w : ℂ}
    (ha : (a.toBall prec).Contains z) (hb : (b.toBall prec).Contains w)
    (h : ChecksMul prec out a b) : (out.toBall prec).Contains (z*w) :=
  ComplexBall.coarsen_contains (ComplexBall.mul_contains ha hb) (checksMul_coarsens prec h)

end DyadicBall
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.DyadicBall.mul_contains
