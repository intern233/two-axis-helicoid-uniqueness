import TwoAxisHelicoid.DyadicExpressionTrace

namespace TwoAxisHelicoid.DyadicBall

def inflate (b : DyadicBall) (r : ℕ) : DyadicBall := ⟨b.re, b.im, b.radius+r⟩

theorem toBall_inflate (prec : ℕ) (b : DyadicBall) (r : ℕ) :
    (b.inflate r).toBall prec = (b.toBall prec).inflate ((r : ℚ)/denominator prec) := by
  unfold inflate toBall ComplexBall.inflate
  congr 1
  push_cast
  ring

theorem inflate_contains {prec : ℕ} {b : DyadicBall} {c z : ℂ} {r : ℕ}
    (hc : (b.toBall prec).Contains c)
    (hz : ‖z-c‖ ≤ (r : ℝ)/(denominator prec : ℝ)) :
    ((b.inflate r).toBall prec).Contains z := by
  rw [toBall_inflate]
  apply ComplexBall.inflate_contains hc
  simpa using hz

end TwoAxisHelicoid.DyadicBall
