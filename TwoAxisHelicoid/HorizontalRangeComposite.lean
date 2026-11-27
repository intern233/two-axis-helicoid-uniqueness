import TwoAxisHelicoid.HorizontalRangeCell
import TwoAxisHelicoid.HorizontalPrefixIntegral
import TwoAxisHelicoid.AllHorizontalRegularity

namespace TwoAxisHelicoid
open ComplexBall

theorem horizontal_range_half_contains {K N : ℕ} (hN : 0 < N)
    (s : HorizontalRangeSetup) (hs : s.Valid) (q : QuadratureRule K) (order : ℕ)
    (hqexact : q.ExactTo order) (hqnodes : q.NodesInUnit)
    {tlo thi alo ahi : ℚ} (p : RangeDyadicParameters)
    (hp : p.HorizontalValid s tlo thi alo ahi)
    (cells : Fin N → HorizontalRangeCell K) (R : ℚ)
    (hcheck : ∀ i : Fin N, (cells i).Valid s q order p (horizontalCellCenter (2*N) i)
      (horizontalCellRadius (2*N)) R)
    {t a : ℝ} (htl : (tlo : ℝ) ≤ t) (htu : t ≤ (thi : ℝ))
    (hal : (alo : ℝ) ≤ a) (hau : a ≤ (ahi : ℝ)) :
    (combineHorizontalCells (fun i => ((cells i).output.toBall s.config.prec))).Contains
      (∫ u : ℝ in (-1)..0, thetaA t a ((u : ℂ)+Complex.I*((t/2 : ℝ) : ℂ))) := by
  have hb (i : Fin N) := (cells i).sound s hs q order hqexact hqnodes p hp htl htu hal hau
    (horizontalCellCenter (2*N) i) (horizontalCellRadius (2*N)) R (hcheck i)
  have hout := scale_contains (sumBalls_contains (fun i => (hb i).1)) (horizontalCellRadius N)
  have hi := horizontal_half_composite_integral hN (thetaA t a) (t/2) (fun i => by
    apply horizontal_cell_intervalIntegrable (R := (R : ℝ))
      (by exact_mod_cast (hcheck i).1) (by exact_mod_cast (hcheck i).2.1.le)
    simpa only [Complex.ofReal_ratCast] using (hb i).2)
  simp only [Complex.ofReal_ratCast] at hi
  rw [← hi]
  exact hout

theorem horizontal_range_half_bounds {K N : ℕ} (hN : 0 < N)
    (s : HorizontalRangeSetup) (hs : s.Valid) (q : QuadratureRule K) (order : ℕ)
    (hqexact : q.ExactTo order) (hqnodes : q.NodesInUnit)
    {tlo thi alo ahi : ℚ} (p : RangeDyadicParameters)
    (hp : p.HorizontalValid s tlo thi alo ahi)
    (cells : Fin N → HorizontalRangeCell K) (R lo hi : ℚ)
    (hcheck : ∀ i : Fin N, (cells i).Valid s q order p (horizontalCellCenter (2*N) i)
      (horizontalCellRadius (2*N)) R)
    (hlo : lo ≤ (combineHorizontalCells (fun i => ((cells i).output.toBall s.config.prec))).center.re-
      (combineHorizontalCells (fun i => ((cells i).output.toBall s.config.prec))).radius)
    (hhi : (combineHorizontalCells (fun i => ((cells i).output.toBall s.config.prec))).center.re+
      (combineHorizontalCells (fun i => ((cells i).output.toBall s.config.prec))).radius ≤ hi)
    {t a : ℝ} (htl : (tlo : ℝ) ≤ t) (htu : t ≤ (thi : ℝ))
    (hal : (alo : ℝ) ≤ a) (hau : a ≤ (ahi : ℝ)) :
    (lo : ℝ) ≤ thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a ≤ (hi : ℝ) := by
  have hb := re_bounds (horizontal_range_half_contains hN s hs q order hqexact hqnodes
    p hp cells R hcheck htl htu hal hau)
  have ht : 0 < t := (s.lower_pos hs).trans_le
    ((Rat.cast_le.mpr hp.1).trans htl)
  rw [horizontal_period_half ht a]
  constructor
  · exact (Rat.cast_le.mpr hlo).trans (by simpa using hb.1)
  · apply le_trans ?_ (Rat.cast_le.mpr hhi)
    simpa using hb.2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.horizontal_range_half_bounds
