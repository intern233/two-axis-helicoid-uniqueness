import TwoAxisHelicoid.DyadicBallInverse

namespace TwoAxisHelicoid.DyadicBall

def neg (a : DyadicBall) : DyadicBall := ⟨-a.re, -a.im, a.radius⟩

theorem neg_toBall (prec : ℕ) (a : DyadicBall) :
    (a.neg.toBall prec) = ComplexBall.neg (a.toBall prec) := by
  simp [neg, toBall, ComplexBall.neg, QComplex.neg, neg_div]

theorem neg_contains {prec : ℕ} {a : DyadicBall} {z : ℂ}
    (ha : (a.toBall prec).Contains z) : (a.neg.toBall prec).Contains (-z) := by
  rw [neg_toBall]
  exact ComplexBall.neg_contains ha

def Coarsens (out a : DyadicBall) : Prop :=
  |out.re-a.re|+|out.im-a.im|+(a.radius : ℤ) ≤ out.radius

instance (out a : DyadicBall) : Decidable (Coarsens out a) := by unfold Coarsens; infer_instance

theorem coarsens_toBall (prec : ℕ) {out a : DyadicBall} (h : out.Coarsens a) :
    (out.toBall prec).coarsens (a.toBall prec) := by
  have hh : ChecksAdd out a zero := by simpa only [Coarsens, ChecksAdd, zero, Nat.cast_zero, add_zero] using h
  have hs := checksAdd_coarsens prec hh
  simpa [zero, toBall, ComplexBall.add, QComplex.add] using hs

theorem coarsen_contains {prec : ℕ} {out a : DyadicBall} {z : ℂ}
    (ha : (a.toBall prec).Contains z) (h : out.Coarsens a) : (out.toBall prec).Contains z :=
  ComplexBall.coarsen_contains ha (coarsens_toBall prec h)

end TwoAxisHelicoid.DyadicBall

#print axioms TwoAxisHelicoid.DyadicBall.coarsen_contains
