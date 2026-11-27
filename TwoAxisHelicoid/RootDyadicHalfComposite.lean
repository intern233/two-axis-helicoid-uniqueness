import TwoAxisHelicoid.RootDyadicCell
import TwoAxisHelicoid.HorizontalPrefixIntegral
import TwoAxisHelicoid.RootHorizontalHalf

namespace TwoAxisHelicoid
open ComplexBall Metric

theorem dyadic_horizontal_half_contains {N : ℕ} (hN : 0 < N)
    {tlo thi alo ahi : ℚ} (p : RootDyadicParameters) (hp : p.Valid tlo thi alo ahi)
    (cells : Fin N → RootDyadicCell) (R : ℚ)
    (hcheck : ∀ i : Fin N, (cells i).Valid p (horizontalCellCenter (2*N) i)
      (horizontalCellRadius (2*N)) R)
    {t a : ℝ} (htl : (tlo : ℝ) ≤ t) (htu : t ≤ (thi : ℝ))
    (hal : (alo : ℝ) ≤ a) (hau : a ≤ (ahi : ℝ)) :
    (combineHorizontalCells (fun i => ((cells i).output.toBall rootDyadicConfig.prec))).Contains
      (∫ u : ℝ in (-1)..0, thetaA t a ((u : ℂ)+Complex.I*((t/2 : ℝ) : ℂ))) := by
  have hb (i : Fin N) := (cells i).sound p hp htl htu hal hau
    (horizontalCellCenter (2*N) i) (horizontalCellRadius (2*N)) R (hcheck i)
  have hs := scale_contains (sumBalls_contains (fun i => (hb i).1)) (horizontalCellRadius N)
  have hi := horizontal_half_composite_integral hN (thetaA t a) (t/2) (fun i => by
    apply horizontal_cell_intervalIntegrable (R := (R : ℝ))
      (by exact_mod_cast (hcheck i).1) (by exact_mod_cast (hcheck i).2.1.le)
    simpa only [Complex.ofReal_ratCast] using (hb i).2)
  simp only [Complex.ofReal_ratCast] at hi
  rw [← hi]
  exact hs

theorem dyadic_horizontal_half_bounds {N : ℕ} (hN : 0 < N)
    {tlo thi alo ahi : ℚ} (p : RootDyadicParameters) (hp : p.Valid tlo thi alo ahi)
    (cells : Fin N → RootDyadicCell) (R lo hi : ℚ)
    (hcheck : ∀ i : Fin N, (cells i).Valid p (horizontalCellCenter (2*N) i)
      (horizontalCellRadius (2*N)) R)
    (hlo : lo ≤ (combineHorizontalCells (fun i => ((cells i).output.toBall rootDyadicConfig.prec))).center.re-
      (combineHorizontalCells (fun i => ((cells i).output.toBall rootDyadicConfig.prec))).radius)
    (hhi : (combineHorizontalCells (fun i => ((cells i).output.toBall rootDyadicConfig.prec))).center.re+
      (combineHorizontalCells (fun i => ((cells i).output.toBall rootDyadicConfig.prec))).radius ≤ hi)
    {t a : ℝ} (htl : (tlo : ℝ) ≤ t) (htu : t ≤ (thi : ℝ))
    (hrootl : (rootTLower : ℝ) ≤ t) (hrootu : t ≤ (rootTUpper : ℝ))
    (hal : (alo : ℝ) ≤ a) (hau : a ≤ (ahi : ℝ)) :
    (lo : ℝ) ≤ thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a ≤ (hi : ℝ) := by
  have hb := re_bounds (dyadic_horizontal_half_contains hN p hp cells R hcheck htl htu hal hau)
  rw [root_horizontal_period_half hrootl hrootu a]
  constructor
  · calc
      _ ≤ (((combineHorizontalCells (fun i => ((cells i).output.toBall rootDyadicConfig.prec))).center.re-
          (combineHorizontalCells (fun i => ((cells i).output.toBall rootDyadicConfig.prec))).radius : ℚ) : ℝ) := Rat.cast_le.mpr hlo
      _ ≤ _ := by simpa using hb.1
  · calc
      _ ≤ (((combineHorizontalCells (fun i => ((cells i).output.toBall rootDyadicConfig.prec))).center.re+
          (combineHorizontalCells (fun i => ((cells i).output.toBall rootDyadicConfig.prec))).radius : ℚ) : ℝ) := by simpa using hb.2
      _ ≤ _ := Rat.cast_le.mpr hhi

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.dyadic_horizontal_half_bounds
