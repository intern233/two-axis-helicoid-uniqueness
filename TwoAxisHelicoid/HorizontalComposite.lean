import TwoAxisHelicoid.HorizontalCellCertificate

namespace TwoAxisHelicoid
open ComplexBall Metric Set MeasureTheory

theorem normalizedIntegral_cell_eq (f : ℂ → ℂ) (x y h : ℝ) :
    (h : ℂ)*normalizedIntegral f ((x : ℂ)+Complex.I*y) h =
      (1/2 : ℂ)*(∫ u : ℝ in (x-h)..(x+h), f ((u : ℂ)+Complex.I*y)) := by
  have ha : (fun u : ℝ => f (((x : ℂ)+Complex.I*y)+(h : ℂ)*(u : ℂ))) =
      (fun u : ℝ => f (((x+h*u : ℝ) : ℂ)+Complex.I*y)) := by
    funext u
    congr 1
    push_cast
    ring
  have hs := intervalIntegral.smul_integral_comp_add_mul
    (fun u : ℝ => f ((u : ℂ)+Complex.I*y)) (a := (-1 : ℝ)) (b := 1) h x
  simp only [Complex.real_smul, mul_neg_one, mul_one, ← sub_eq_add_neg] at hs
  unfold normalizedIntegral
  rw [ha]
  calc
    _ = (1/2 : ℂ)*((h : ℂ)*(∫ u : ℝ in (-1)..1,
        f (((x+h*u : ℝ) : ℂ)+Complex.I*y))) := by ring
    _ = _ := by rw [hs]

theorem horizontal_cell_intervalIntegrable {f : ℂ → ℂ} {x y h R : ℝ}
    (hh : 0 ≤ h) (hhR : h ≤ R)
    (hf : DiffContOnCl ℂ f (ball ((x : ℂ)+Complex.I*y) R)) :
    IntervalIntegrable (fun u : ℝ => f ((u : ℂ)+Complex.I*y)) volume (x-h) (x+h) := by
  have hm : MapsTo (fun u : ℝ => (u : ℂ)+Complex.I*y) (Icc (x-h) (x+h))
      (closedBall ((x : ℂ)+Complex.I*y) R) := by
    intro u hu
    apply mem_closedBall_iff_norm.mpr
    have he : ((u : ℂ)+Complex.I*y)-((x : ℂ)+Complex.I*y) = ((u-x : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩).trans hhR
  exact (hf.continuousOn_ball.comp (by fun_prop) hm).intervalIntegrable_of_Icc (by linarith)

def horizontalCellCenter (K k : ℕ) : ℚ := -1+(2*k+1 : ℚ)/K
def horizontalCellRadius (K : ℕ) : ℚ := 1/K

theorem horizontal_composite_integral {K : ℕ} (hK : 0 < K) (f : ℂ → ℂ) (y : ℝ)
    (hint : ∀ i : Fin K, IntervalIntegrable (fun u : ℝ => f ((u : ℂ)+Complex.I*y)) volume
      ((horizontalCellCenter K i : ℝ)-horizontalCellRadius K)
      ((horizontalCellCenter K i : ℝ)+horizontalCellRadius K)) :
    ((horizontalCellRadius K : ℚ) : ℂ)*
      (∑ i : Fin K, normalizedIntegral f
        (((horizontalCellCenter K i : ℝ) : ℂ)+Complex.I*y) (horizontalCellRadius K : ℝ)) =
      (1/2 : ℂ)*(∫ u : ℝ in (-1)..1, f ((u : ℂ)+Complex.I*y)) := by
  let boundary (k : ℕ) : ℝ := -1+2*k/K
  have hKn : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hl (k : ℕ) : (horizontalCellCenter K k : ℝ)-horizontalCellRadius K = boundary k := by
    dsimp [horizontalCellCenter, horizontalCellRadius, boundary]
    push_cast
    ring
  have hr (k : ℕ) : (horizontalCellCenter K k : ℝ)+horizontalCellRadius K = boundary (k+1) := by
    dsimp [horizontalCellCenter, horizontalCellRadius, boundary]
    push_cast
    ring
  have hint' : ∀ k < K, IntervalIntegrable (fun u : ℝ => f ((u : ℂ)+Complex.I*y)) volume
      (boundary k) (boundary (k+1)) := by
    intro k hk
    simpa only [hl, hr] using hint ⟨k, hk⟩
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint'
  have hend0 : boundary 0 = -1 := by simp [boundary]
  have hendK : boundary K = 1 := by dsimp [boundary]; field_simp; ring
  rw [hend0, hendK] at hsum
  rw [Finset.mul_sum]
  have heach (i : Fin K) : ((horizontalCellRadius K : ℚ) : ℂ)*
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
    (fun k => ∫ u : ℝ in boundary k..boundary (k+1), f ((u : ℂ)+Complex.I*y)) K

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.horizontal_composite_integral
