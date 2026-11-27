import TwoAxisHelicoid.RangeDerivativeCell
import TwoAxisHelicoid.HorizontalPrefixIntegral

namespace TwoAxisHelicoid
open ComplexBall

theorem range_derivative_half_contains (s : RangeCertificateSetup) (hs : s.Valid)
    {tlo thi alo ahi : ℚ} {N : ℕ} (hN : 0 < N)
    (p : RangeDerivativeParameters) (hp : p.Valid s tlo thi alo ahi) (cells : Fin N → RangeDerivativeCell) (R : ℚ)
    (hcheck : ∀ i : Fin N, (cells i).Valid s p (horizontalCellCenter (2*N) i)
      (horizontalCellRadius (2*N)) R)
    {t a : ℝ} (htl : (tlo : ℝ) ≤ t) (htu : t ≤ (thi : ℝ))
    (hal : (alo : ℝ) ≤ a) (hau : a ≤ (ahi : ℝ)) :
    (combineHorizontalCells (fun i => ((cells i).outputA.toBall s.config.prec))).Contains
      (∫ x : ℝ in (-1)..0, thetaAa t a ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ))) ∧
    (combineHorizontalCells (fun i => ((cells i).outputT.toBall s.config.prec))).Contains
      (∫ x : ℝ in (-1)..0, thetaAtMidline t a ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ))) := by
  have he := p.sound s hs hp htl htu hal hau
  have hb (i : Fin N) := (cells i).sound s hs p he
    (horizontalCellCenter (2*N) i) (horizontalCellRadius (2*N)) R (hcheck i)
  have hA := horizontal_half_composite_integral hN (thetaAa t a) (t/2) (fun i => by
    apply horizontal_cell_intervalIntegrable (R := (R : ℝ))
      (by exact_mod_cast (hcheck i).1) (by exact_mod_cast (hcheck i).2.1.le)
    simpa only [Complex.ofReal_ratCast] using (hb i).2.2.1)
  have hT := horizontal_half_composite_integral hN (thetaAtMidline t a) (t/2) (fun i => by
    apply horizontal_cell_intervalIntegrable (R := (R : ℝ))
      (by exact_mod_cast (hcheck i).1) (by exact_mod_cast (hcheck i).2.1.le)
    simpa only [Complex.ofReal_ratCast] using (hb i).2.2.2)
  simp only [Complex.ofReal_ratCast] at hA hT
  constructor
  · rw [← hA]
    exact scale_contains (sumBalls_contains (fun i => (hb i).1)) (horizontalCellRadius N)
  · rw [← hT]
    exact scale_contains (sumBalls_contains (fun i => (hb i).2.1)) (horizontalCellRadius N)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.range_derivative_half_contains
