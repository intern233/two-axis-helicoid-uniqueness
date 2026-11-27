import TwoAxisHelicoid.RootDerivativeCell
import TwoAxisHelicoid.HorizontalPrefixIntegral

namespace TwoAxisHelicoid
open ComplexBall

theorem root_derivative_half_contains {N : ℕ} (hN : 0 < N)
    (p : RootDerivativeParameters) (hp : p.Valid) (cells : Fin N → RootDerivativeCell) (R : ℚ)
    (hcheck : ∀ i : Fin N, (cells i).Valid p (horizontalCellCenter (2*N) i)
      (horizontalCellRadius (2*N)) R)
    {t a : ℝ} (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ))
    (hal : (rootALower : ℝ) ≤ a) (hau : a ≤ (rootAUpper : ℝ)) :
    (combineHorizontalCells (fun i => ((cells i).outputA.toBall rootDyadicConfig.prec))).Contains
      (∫ x : ℝ in (-1)..0, thetaAa t a ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ))) ∧
    (combineHorizontalCells (fun i => ((cells i).outputT.toBall rootDyadicConfig.prec))).Contains
      (∫ x : ℝ in (-1)..0, thetaAtMidline t a ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ))) := by
  have hb (i : Fin N) := (cells i).sound p hp htl htu hal hau
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

#print axioms TwoAxisHelicoid.root_derivative_half_contains
