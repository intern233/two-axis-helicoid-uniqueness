import TwoAxisHelicoid.RootDyadicCell

namespace TwoAxisHelicoid
open ComplexBall Metric

theorem dyadic_horizontal_integral_contains {K : ℕ} (hK : 0 < K)
    {tlo thi alo ahi : ℚ} (p : RootDyadicParameters) (hp : p.Valid tlo thi alo ahi)
    (cells : Fin K → RootDyadicCell) (R : ℚ)
    (hcheck : ∀ i : Fin K, (cells i).Valid p (horizontalCellCenter K i) (horizontalCellRadius K) R)
    {t a : ℝ} (htl : (tlo : ℝ) ≤ t) (htu : t ≤ (thi : ℝ))
    (hal : (alo : ℝ) ≤ a) (hau : a ≤ (ahi : ℝ)) :
    (combineHorizontalCells (fun i => ((cells i).output.toBall rootDyadicConfig.prec))).Contains
      ((1/2 : ℂ)*(∫ u : ℝ in (-1)..1, thetaA t a ((u : ℂ)+Complex.I*((t/2 : ℝ) : ℂ)))) := by
  have hb (i : Fin K) := (cells i).sound p hp htl htu hal hau
    (horizontalCellCenter K i) (horizontalCellRadius K) R (hcheck i)
  have hs := scale_contains (sumBalls_contains (fun i => (hb i).1)) (horizontalCellRadius K)
  have hi := horizontal_composite_integral hK (thetaA t a) (t/2) (fun i => by
    apply horizontal_cell_intervalIntegrable (R := (R : ℝ))
      (by exact_mod_cast (hcheck i).1) (by exact_mod_cast (hcheck i).2.1.le)
    simpa only [Complex.ofReal_ratCast] using (hb i).2)
  simp only [Complex.ofReal_ratCast] at hi
  rw [← hi]
  exact hs

theorem dyadic_horizontal_integral_bounds {K : ℕ} (hK : 0 < K)
    {tlo thi alo ahi : ℚ} (p : RootDyadicParameters) (hp : p.Valid tlo thi alo ahi)
    (cells : Fin K → RootDyadicCell) (R lo hi : ℚ)
    (hcheck : ∀ i : Fin K, (cells i).Valid p (horizontalCellCenter K i) (horizontalCellRadius K) R)
    (hlo : lo ≤ (combineHorizontalCells (fun i => ((cells i).output.toBall rootDyadicConfig.prec))).center.re-
      (combineHorizontalCells (fun i => ((cells i).output.toBall rootDyadicConfig.prec))).radius)
    (hhi : (combineHorizontalCells (fun i => ((cells i).output.toBall rootDyadicConfig.prec))).center.re+
      (combineHorizontalCells (fun i => ((cells i).output.toBall rootDyadicConfig.prec))).radius ≤ hi)
    {t a : ℝ} (htl : (tlo : ℝ) ≤ t) (htu : t ≤ (thi : ℝ))
    (hal : (alo : ℝ) ≤ a) (hau : a ≤ (ahi : ℝ)) :
    (lo : ℝ) ≤ thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a ≤ (hi : ℝ) := by
  have hb := re_bounds (dyadic_horizontal_integral_contains hK p hp cells R hcheck htl htu hal hau)
  have hb' : (((combineHorizontalCells (fun i => ((cells i).output.toBall rootDyadicConfig.prec))).center.re-
      (combineHorizontalCells (fun i => ((cells i).output.toBall rootDyadicConfig.prec))).radius : ℚ) : ℝ) ≤
        thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a ≤
      (((combineHorizontalCells (fun i => ((cells i).output.toBall rootDyadicConfig.prec))).center.re+
      (combineHorizontalCells (fun i => ((cells i).output.toBall rootDyadicConfig.prec))).radius : ℚ) : ℝ) := by
    simpa [thetaHorizontalPeriod, Complex.mul_re] using hb
  exact ⟨(Rat.cast_le.mpr hlo).trans hb'.1, hb'.2.trans (Rat.cast_le.mpr hhi)⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.dyadic_horizontal_integral_bounds
