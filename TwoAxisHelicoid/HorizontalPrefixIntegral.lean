import TwoAxisHelicoid.HorizontalComposite

namespace TwoAxisHelicoid
open ComplexBall Metric Set MeasureTheory

theorem horizontal_composite_prefix {K L : ℕ} (f : ℂ → ℂ) (y : ℝ)
    (hint : ∀ i : Fin L, IntervalIntegrable (fun u : ℝ => f ((u : ℂ)+Complex.I*y)) volume
      ((horizontalCellCenter K i : ℝ)-horizontalCellRadius K)
      ((horizontalCellCenter K i : ℝ)+horizontalCellRadius K)) :
    ((horizontalCellRadius K : ℚ) : ℂ)*
      (∑ i : Fin L, normalizedIntegral f
        (((horizontalCellCenter K i : ℝ) : ℂ)+Complex.I*y) (horizontalCellRadius K : ℝ)) =
      (1/2 : ℂ)*(∫ u : ℝ in (-1)..(-1+2*L/K), f ((u : ℂ)+Complex.I*y)) := by
  let boundary (k : ℕ) : ℝ := -1+2*k/K
  have hl (k : ℕ) : (horizontalCellCenter K k : ℝ)-horizontalCellRadius K = boundary k := by
    dsimp [horizontalCellCenter, horizontalCellRadius, boundary]
    push_cast
    ring
  have hr (k : ℕ) : (horizontalCellCenter K k : ℝ)+horizontalCellRadius K = boundary (k+1) := by
    dsimp [horizontalCellCenter, horizontalCellRadius, boundary]
    push_cast
    ring
  have hint' : ∀ k < L, IntervalIntegrable (fun u : ℝ => f ((u : ℂ)+Complex.I*y)) volume
      (boundary k) (boundary (k+1)) := by
    intro k hk
    simpa only [hl, hr] using hint ⟨k, hk⟩
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint'
  have hend0 : boundary 0 = -1 := by simp [boundary]
  rw [hend0] at hsum
  rw [Finset.mul_sum]
  have heach (i : Fin L) : ((horizontalCellRadius K : ℚ) : ℂ)*
      normalizedIntegral f (((horizontalCellCenter K i : ℝ) : ℂ)+Complex.I*y)
        (horizontalCellRadius K : ℝ) =
      (1/2 : ℂ)*(∫ u : ℝ in boundary i..boundary (i+1), f ((u : ℂ)+Complex.I*y)) := by
    simpa only [Complex.ofReal_ratCast, hl, hr] using
      normalizedIntegral_cell_eq f (horizontalCellCenter K i) y (horizontalCellRadius K)
  simp_rw [heach]
  rw [← Finset.mul_sum]
  congr 1
  rw [← hsum]
  exact Fin.sum_univ_eq_sum_range
    (fun k => ∫ u : ℝ in boundary k..boundary (k+1), f ((u : ℂ)+Complex.I*y)) L

theorem horizontal_half_composite_integral {N : ℕ} (hN : 0 < N) (f : ℂ → ℂ) (y : ℝ)
    (hint : ∀ i : Fin N, IntervalIntegrable (fun u : ℝ => f ((u : ℂ)+Complex.I*y)) volume
      ((horizontalCellCenter (2*N) i : ℝ)-horizontalCellRadius (2*N))
      ((horizontalCellCenter (2*N) i : ℝ)+horizontalCellRadius (2*N))) :
    ((horizontalCellRadius N : ℚ) : ℂ)*
      (∑ i : Fin N, normalizedIntegral f
        (((horizontalCellCenter (2*N) i : ℝ) : ℂ)+Complex.I*y) (horizontalCellRadius (2*N) : ℝ)) =
      (∫ u : ℝ in (-1)..0, f ((u : ℂ)+Complex.I*y)) := by
  have hp := horizontal_composite_prefix f y hint
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : (-1+2*(N : ℝ)/(2*N) : ℝ) = 0 := by field_simp; ring
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hp
  rw [he] at hp
  have hscale : ((horizontalCellRadius N : ℚ) : ℂ) =
      2*((horizontalCellRadius (2*N) : ℚ) : ℂ) := by
    simp [horizontalCellRadius]
    ring
  rw [hscale, mul_assoc, hp]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.horizontal_half_composite_integral
