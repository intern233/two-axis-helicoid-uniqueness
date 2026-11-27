import TwoAxisHelicoid.ZetaAxisIntegral

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology Interval
attribute [local irreducible] thetaZeta

theorem zetaAxisDifference_even (t a y : ℝ) :
    zetaAxisDifference t a (-y) = zetaAxisDifference t a y := by
  unfold zetaAxisDifference
  rw [Complex.ofReal_neg]
  rw [show -(a : ℂ)+(-(y : ℂ))*I = -((a : ℂ)+(y : ℂ)*I) by ring,
    show (a : ℂ)+(-(y : ℂ))*I = -(-(a : ℂ)+(y : ℂ)*I) by ring,
    thetaZeta_neg,thetaZeta_neg]
  ring

theorem zetaAxisDifference_integral_half {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    (∫ y : ℝ in 0..2*t, zetaAxisDifference t a y) =
      2*(∫ y : ℝ in 0..t, zetaAxisDifference t a y) := by
  have hc := zetaAxisDifference_continuous ht ha
  have he := intervalIntegral.integral_comp_neg (f := zetaAxisDifference t a) (a := 0) (b := t)
  simp only [zetaAxisDifference_even,neg_zero] at he
  rw [zetaAxisDifference_integral_centered ht ha,
    ← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := volume) (-t) 0) (hc.intervalIntegrable (μ := volume) 0 t),
    ← he]
  ring

/-- Exact value on the half-axis containing the first endpoint. Its limiting
constant is the endpoint contribution which cannot be discarded. -/
theorem thetaZeta_first_half_integral {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    I*(∫ y : ℝ in 0..t, zetaAxisDifference t a y) =
      -(a : ℂ)*zetaImaginaryQuasi t-Real.pi*I := by
  have h := thetaZeta_axis_difference_integral ht ha
  rw [zetaAxisDifference_integral_half ht ha] at h
  linear_combination (1/2 : ℂ)*h

theorem thetaZeta_second_half_integral {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    I*(∫ y : ℝ in t..2*t, zetaAxisDifference t a y) =
      -(a : ℂ)*zetaImaginaryQuasi t-Real.pi*I := by
  have hc := zetaAxisDifference_continuous ht ha
  have h := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 t) (hc.intervalIntegrable (μ := volume) t (2*t))
  rw [zetaAxisDifference_integral_half ht ha] at h
  have he := thetaZeta_first_half_integral ht ha
  linear_combination I*h+he

theorem thetaZeta_first_endpoint_limit {t : ℝ} (ht : 0 < t) :
    Tendsto (fun a : ℝ => I*(∫ y : ℝ in 0..t, zetaAxisDifference t a y))
      (𝓝[>] 0) (𝓝 (-(Real.pi : ℂ)*I)) := by
  have hc : Continuous (fun a : ℝ => -(a : ℂ)*zetaImaginaryQuasi t-(Real.pi : ℂ)*I) := by fun_prop
  have hl : Tendsto (fun a : ℝ => -(a : ℂ)*zetaImaginaryQuasi t-(Real.pi : ℂ)*I)
      (𝓝[>] 0) (𝓝 (-(Real.pi : ℂ)*I)) := by
    simpa only [Complex.ofReal_zero,neg_zero,zero_mul,zero_sub,neg_mul] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with a ha ha1
  exact (thetaZeta_first_half_integral ht ⟨ha,ha1⟩).symm

theorem thetaZeta_second_endpoint_limit {t : ℝ} (ht : 0 < t) :
    Tendsto (fun a : ℝ => I*(∫ y : ℝ in t..2*t, zetaAxisDifference t a y))
      (𝓝[>] 0) (𝓝 (-(Real.pi : ℂ)*I)) := by
  apply (thetaZeta_first_endpoint_limit ht).congr'
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with a ha ha1
  rw [thetaZeta_first_half_integral ht ⟨ha,ha1⟩,thetaZeta_second_half_integral ht ⟨ha,ha1⟩]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaZeta_first_endpoint_limit
#print axioms TwoAxisHelicoid.thetaZeta_second_endpoint_limit
