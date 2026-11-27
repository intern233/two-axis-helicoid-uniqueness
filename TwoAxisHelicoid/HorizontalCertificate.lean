import TwoAxisHelicoid.HorizontalComposite

namespace TwoAxisHelicoid
open ComplexBall

def sumBalls {K : ℕ} (b : Fin K → ComplexBall) : ComplexBall :=
  ⟨⟨∑ i, (b i).center.re, ∑ i, (b i).center.im⟩, ∑ i, (b i).radius⟩

theorem sumBalls_contains {K : ℕ} {b : Fin K → ComplexBall} {v : Fin K → ℂ}
    (hb : ∀ i, (b i).Contains (v i)) : (sumBalls b).Contains (∑ i, v i) := by
  have hc : (sumBalls b).center.val = ∑ i, (b i).center.val := by
    apply Complex.ext <;> simp [sumBalls, QComplex.val]
  unfold Contains
  rw [hc, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖v i-(b i).center.val‖ := norm_sum_le _ _
    _ ≤ ∑ i, ((b i).radius : ℝ) := Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by simp [sumBalls]

def combineHorizontalCells {K : ℕ} (b : Fin K → ComplexBall) : ComplexBall :=
  scale (horizontalCellRadius K) (sumBalls b)

theorem certified_horizontal_integral_contains {K : ℕ} (hK : 0 < K)
    (cfg : BallConfig) (N : ℕ) (tlo thi alo ahi R : ℚ) (out : Fin K → ComplexBall)
    (hcheck : ∀ i : Fin K, certifiesHorizontalCell cfg N tlo thi alo ahi
      (horizontalCellCenter K i) (horizontalCellRadius K) R (out i)) {t a : ℝ}
    (htl : (tlo : ℝ) ≤ t) (htu : t ≤ (thi : ℝ))
    (hal : (alo : ℝ) ≤ a) (hau : a ≤ (ahi : ℝ)) :
    (combineHorizontalCells out).Contains
      ((1/2 : ℂ)*(∫ u : ℝ in (-1)..1, thetaA t a ((u : ℂ)+Complex.I*((t/2 : ℝ) : ℂ)))) := by
  have hb (i : Fin K) := certified_horizontal_cell_contains cfg N tlo thi alo ahi
    (horizontalCellCenter K i) (horizontalCellRadius K) R (out i) (hcheck i) htl htu hal hau
  have hs := scale_contains (sumBalls_contains hb) (horizontalCellRadius K)
  have hi := horizontal_composite_integral hK (thetaA t a) (t/2) (fun i => by
    have hc := certified_horizontal_cell_holomorphic cfg N tlo thi alo ahi
      (horizontalCellCenter K i) (horizontalCellRadius K) R (out i) (hcheck i) htl htu hal hau
    apply horizontal_cell_intervalIntegrable (R := (R : ℝ))
      (by exact_mod_cast hc.1) (by exact_mod_cast hc.2.1.le)
    simpa only [Complex.ofReal_ratCast] using hc.2.2)
  simp only [Complex.ofReal_ratCast] at hi
  rw [← hi]
  exact hs

theorem certified_horizontal_integral_bounds {K : ℕ} (hK : 0 < K)
    (cfg : BallConfig) (N : ℕ) (tlo thi alo ahi R : ℚ) (out : Fin K → ComplexBall)
    (hcheck : ∀ i : Fin K, certifiesHorizontalCell cfg N tlo thi alo ahi
      (horizontalCellCenter K i) (horizontalCellRadius K) R (out i)) {t a : ℝ}
    (htl : (tlo : ℝ) ≤ t) (htu : t ≤ (thi : ℝ))
    (hal : (alo : ℝ) ≤ a) (hau : a ≤ (ahi : ℝ)) :
    ((combineHorizontalCells out).center.re-(combineHorizontalCells out).radius : ℚ) ≤
      thetaHorizontalPeriod t a ∧
    thetaHorizontalPeriod t a ≤
      ((combineHorizontalCells out).center.re+(combineHorizontalCells out).radius : ℚ) := by
  have hb := re_bounds (certified_horizontal_integral_contains hK cfg N tlo thi alo ahi R out
    hcheck htl htu hal hau)
  simpa [thetaHorizontalPeriod, Complex.mul_re] using hb

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.certified_horizontal_integral_bounds
