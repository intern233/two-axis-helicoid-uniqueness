import TwoAxisHelicoid.AxisCoordinateDifferentials
import TwoAxisHelicoid.CoordinateMetricEnd

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

theorem coordinateMetric_at_lattice_lower_bound {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) {ω : ℂ}
    (hω : ω ∈ (rhombicPeriodPair t ht).lattice) :
    ∀ᶠ z in 𝓝[≠] ω, |c|/(2*‖z-ω‖^2) ≤
      Real.sqrt (nullMetric (coordinateData t a c ht z)) := by
  have hs : Tendsto (fun z : ℂ => z-ω) (𝓝[≠] ω) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [sub_self] using
        (show Tendsto (fun z : ℂ => z-ω) (𝓝[≠] ω) (𝓝 (ω-ω)) from
          (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact sub_ne_zero.mpr hz
  filter_upwards [hs.eventually (coordinateMetric_puncture_lower_bound ht ha hc)] with z hz
  have he := coordinateData_add_lattice (a := a) (c := c) ht (z-ω) ⟨ω,hω⟩
  rw [sub_add_cancel] at he
  rw [← he] at hz
  exact hz

theorem affine_axis_metric_endpoint {t a c b : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (z₀ v : ℂ) (hv : ‖v‖ = 1)
    (hω : z₀+v*(b : ℂ) ∈ (rhombicPeriodPair t ht).lattice) :
    ∀ᶠ (x : ℝ) in 𝓝[≠] b, (|c|/2)/(x-b)^2 ≤
      Real.sqrt (nullMetric (coordinateData t a c ht (z₀+v*(x : ℂ)))) := by
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have hpath : Tendsto (fun x : ℝ => z₀+v*(x : ℂ)) (𝓝[≠] b) (𝓝[≠] (z₀+v*(b : ℂ))) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact (show Continuous (fun x : ℝ => z₀+v*(x : ℂ)) by fun_prop).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      intro he
      have hxC : (x : ℂ) = (b : ℂ) := mul_left_cancel₀ hv0 (add_left_cancel he)
      exact hx (Complex.ofReal_injective hxC)
  filter_upwards [hpath.eventually (coordinateMetric_at_lattice_lower_bound ht ha hc hω)] with x hx
  have hnorm : ‖z₀+v*(x : ℂ)-(z₀+v*(b : ℂ))‖^2 = (x-b)^2 := by
    rw [show z₀+v*(x : ℂ)-(z₀+v*(b : ℂ)) = v*((x-b : ℝ) : ℂ) by push_cast; ring]
    rw [norm_mul,hv,one_mul,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [hnorm] at hx
  simpa only [div_div] using hx

theorem coordinateMetric_horizontal_axis {t a c : ℝ} (ht : 0 < t) (x : ℝ) :
    Real.sqrt (nullMetric (coordinateData t a c ht x)) =
      |(coordinateData t a c ht x 0).re| := by
  have h := coordinateData_horizontal_axis (a := a) (c := c) ht x
  simp [nullMetric,h.1,h.2,Real.sqrt_sq_eq_abs]

theorem coordinateMetric_vertical_axis {t a c y : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (-t) t) :
    Real.sqrt (nullMetric (coordinateData t a c ht (1+I*y))) =
      |(I*coordinateData t a c ht (1+I*y) 2).re| := by
  have hz := rhombic_vertical_axis_not_mem ht hy
  have h := coordinateData_vertical_axis (a := a) (c := c) ht y
  have he := (complexNull_real_identities (p := coordinateData t a c ht (1+I*y))
    (coordinateData_null ht ha hz)).1
  rw [he,h.1,h.2]
  simp [Complex.mul_re,Real.sqrt_sq_eq_abs]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.affine_axis_metric_endpoint
