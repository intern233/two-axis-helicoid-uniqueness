import TwoAxisHelicoid.JacobiRangeCell

namespace TwoAxisHelicoid
open Complex ComplexBall MeasureTheory
set_option maxHeartbeats 800000
attribute [local irreducible] thetaA

def jacobiCellCenter (boundary : ℕ → ℚ) (i : ℕ) : ℚ := (boundary i+boundary (i+1))/2
def jacobiCellRadius (boundary : ℕ → ℚ) (i : ℕ) : ℚ := (boundary (i+1)-boundary i)/2

theorem nonuniform_normalized_integral_sum (N : ℕ) (boundary : ℕ → ℚ)
    (f : ℂ → ℂ) (hf : Continuous (fun u : ℝ => f (u : ℂ))) :
    (∑ i : Fin N, ((boundary (i+1)-boundary i : ℚ) : ℂ)*
      normalizedIntegral f (jacobiCellCenter boundary i : ℂ) (jacobiCellRadius boundary i : ℝ)) =
      ∫ u : ℝ in (boundary 0 : ℝ)..(boundary N : ℝ), f (u : ℂ) := by
  have hint : ∀ k < N, IntervalIntegrable (fun u : ℝ => f (u : ℂ)) volume
      (boundary k : ℝ) (boundary (k+1) : ℝ) := fun k _ => hf.intervalIntegrable _ _
  have hs := intervalIntegral.sum_integral_adjacent_intervals hint
  have heach (i : Fin N) : ((boundary (i+1)-boundary i : ℚ) : ℂ)*
      normalizedIntegral f (jacobiCellCenter boundary i : ℂ) (jacobiCellRadius boundary i : ℝ) =
      ∫ u : ℝ in (boundary i : ℝ)..(boundary (i+1) : ℝ), f (u : ℂ) := by
    have hc := normalizedIntegral_cell_eq f (jacobiCellCenter boundary i) 0 (jacobiCellRadius boundary i)
    simp only [Complex.ofReal_zero, mul_zero, add_zero, Complex.ofReal_ratCast] at hc
    have hl : (jacobiCellCenter boundary i : ℝ)-jacobiCellRadius boundary i = (boundary i : ℝ) := by
      unfold jacobiCellCenter jacobiCellRadius
      push_cast
      ring
    have hr : (jacobiCellCenter boundary i : ℝ)+jacobiCellRadius boundary i = (boundary (i+1) : ℝ) := by
      unfold jacobiCellCenter jacobiCellRadius
      push_cast
      ring
    rw [hl, hr] at hc
    have hw : ((boundary (i+1)-boundary i : ℚ) : ℂ) = 2*(jacobiCellRadius boundary i : ℂ) := by
      unfold jacobiCellRadius
      push_cast
      ring
    rw [hw, mul_assoc, hc]
    ring
  simp_rw [heach]
  rw [← hs]
  exact Fin.sum_univ_eq_sum_range
    (fun k => ∫ u : ℝ in (boundary k : ℝ)..(boundary (k+1) : ℝ), f (u : ℂ)) N

def combineJacobiCells {K N : ℕ} (cfg : BallConfig) (boundary : ℕ → ℚ)
    (cells : Fin N → JacobiRangeCell K) : ComplexBall :=
  sumBalls (fun i => scale (boundary (i+1)-boundary i) ((cells i).output.toBall cfg.prec))

theorem jacobi_composite_contains {K N : ℕ} (cfg : BallConfig) (productError eulerError : ℕ)
    (q : QuadratureRule K) (order : ℕ) (hqexact : q.ExactTo order) (hqnodes : q.NodesInUnit)
    {tlo : ℚ} {t a : ℝ} (ht : 0 < t) (ha0 : 0 < a) (ha1 : a < 1)
    (htl : (tlo : ℝ) ≤ t) (p : DyadicJacobiParameters) (hp : p.Valid cfg productError)
    (hbt : (p.base.height.toBall cfg.prec).Contains (t : ℂ))
    (hba : (p.base.abscissa.toBall cfg.prec).Contains (a : ℂ))
    (boundary : ℕ → ℚ) (hfirst : boundary 0 = -1/2) (hlast : boundary N = 1/2)
    (R : Fin N → ℚ) (right : Fin N → Bool) (cells : Fin N → JacobiRangeCell K)
    (hcheck : ∀ i : Fin N, (cells i).Valid cfg productError eulerError (right i) q order p
      tlo (jacobiCellCenter boundary i) (jacobiCellRadius boundary i) (R i)) :
    (combineJacobiCells cfg boundary cells).Contains
      (∫ u : ℝ in (-1/2)..(1/2), thetaA t a ((u : ℂ)+I*((t/2 : ℝ) : ℂ))) := by
  have hb (i : Fin N) := (cells i).sound cfg productError eulerError (right i) q order
    hqexact hqnodes ht ha0 ha1 htl p hp hbt hba (hcheck i)
  have hout := sumBalls_contains (fun i => scale_contains (hb i).1 (boundary (i+1)-boundary i))
  have he := nonuniform_normalized_integral_sum N boundary
    (fun z : ℂ => thetaA t a (z+I*((t/2 : ℝ) : ℂ))) (horizontal_integrand_continuous ht a)
  rw [he] at hout
  rw [hfirst, hlast] at hout
  simpa only [combineJacobiCells, Rat.cast_div, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] using hout

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobi_composite_contains
