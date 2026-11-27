import TwoAxisHelicoid.AxisPrimitiveLines
import TwoAxisHelicoid.AxisMetricEndpoints
import TwoAxisHelicoid.InverseSquarePrimitive

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
set_option maxHeartbeats 1200000

theorem actual_primitive_horizontal_coordinate_surjective {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    {X : ℂ → Fin 3 → ℝ} (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht) :
    SurjOn (fun x : ℝ => X (x : ℂ) 0) (Ioo (0 : ℝ) 2) univ := by
  apply inverse_square_nonzero_derivative_surjective (C := |c|/2) (by norm_num)
    (div_pos (abs_pos.mpr hc) (by norm_num))
    (fun x hx => actual_primitive_horizontal_hasDerivAt ht hX hx 0)
  · intro x hx
    have hz := real_not_mem_rhombic_lattice_of_pos ht hx.1 hx.2
    have hC := (coordinateData_analyticAt (a := a) (c := c) ht hz).continuousAt.comp
      Complex.continuous_ofReal.continuousAt
    exact (Complex.continuous_re.continuousAt.comp
      ((continuous_apply 0).continuousAt.comp hC)).continuousWithinAt
  · exact fun x hx => coordinateData_horizontal_axis_regular ht ha hc hx
  · have hω : (0 : ℂ)+1*(0 : ℝ) ∈ (rhombicPeriodPair t ht).lattice := by simp
    have h := affine_axis_metric_endpoint ht ha hc 0 1 (by norm_num) hω
    filter_upwards [h.filter_mono (nhdsGT_le_nhdsNE (0 : ℝ))] with x hx
    simpa [coordinateMetric_horizontal_axis] using hx
  · have hω : (0 : ℂ)+1*(2 : ℝ) ∈ (rhombicPeriodPair t ht).lattice := by
      simpa [rhombicPeriodPair] using (rhombicPeriodPair t ht).ω₁_mem_lattice
    have h := affine_axis_metric_endpoint ht ha hc 0 1 (by norm_num) hω
    filter_upwards [h.filter_mono (nhdsLT_le_nhdsNE (2 : ℝ))] with x hx
    simpa [coordinateMetric_horizontal_axis,sub_sq_comm] using hx

theorem actual_primitive_vertical_coordinate_surjective {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    {X : ℂ → Fin 3 → ℝ} (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht) :
    SurjOn (fun y : ℝ => X (1+I*y) 2) (Ioo (-t) t) univ := by
  have htt : -t < t := by linarith
  apply inverse_square_nonzero_derivative_surjective (C := |c|/2) htt
    (div_pos (abs_pos.mpr hc) (by norm_num))
    (fun y hy => actual_primitive_vertical_hasDerivAt ht hX hy 2)
  · intro y hy
    have hz := rhombic_vertical_axis_not_mem ht hy
    have hpath : Continuous (fun u : ℝ => (1 : ℂ)+I*u) := by fun_prop
    have hC : ContinuousAt (fun u : ℝ => coordinateData t a c ht (1+I*u)) y :=
      (coordinateData_analyticAt (a := a) (c := c) ht hz).continuousAt.comp
        (f := fun u : ℝ => 1+I*u) hpath.continuousAt
    exact (Complex.continuous_re.continuousAt.comp
      (continuousAt_const.mul ((continuous_apply 2).continuousAt.comp hC))).continuousWithinAt
  · exact fun y hy => coordinateData_vertical_axis_regular ht ha hc hy
  · have hω : (1 : ℂ)+I*(-t : ℝ) ∈ (rhombicPeriodPair t ht).lattice := by
      apply PeriodPair.mem_lattice.mpr
      refine ⟨1,-1,?_⟩
      simp only [rhombicPeriodPair,Int.cast_one,Int.cast_neg,Complex.ofReal_neg]
      ring
    have h := affine_axis_metric_endpoint ht ha hc 1 I (by norm_num) hω
    filter_upwards [h.filter_mono (nhdsGT_le_nhdsNE (-t)),Ioo_mem_nhdsGT htt] with y hy hmem
    rw [coordinateMetric_vertical_axis ht ha hmem] at hy
    exact hy
  · have hω : (1 : ℂ)+I*(t : ℝ) ∈ (rhombicPeriodPair t ht).lattice :=
      (rhombicPeriodPair t ht).ω₂_mem_lattice
    have h := affine_axis_metric_endpoint ht ha hc 1 I (by norm_num) hω
    filter_upwards [h.filter_mono (nhdsLT_le_nhdsNE t),Ioo_mem_nhdsLT htt] with y hy hmem
    rw [coordinateMetric_vertical_axis ht ha hmem] at hy
    simpa only [sub_sq_comm] using hy

/-- Every genuine global primitive of the actual forms contains both full
orthogonal axes after centering at the common parameter point `1`. -/
theorem actual_primitive_contains_complete_axes {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    {X : ℂ → Fin 3 → ℝ} (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht) :
    (∀ r : ℝ, ∃ z ∉ (rhombicPeriodPair t ht).lattice, X z-X 1 = ![r,0,0]) ∧
    (∀ r : ℝ, ∃ z ∉ (rhombicPeriodPair t ht).lattice, X z-X 1 = ![0,0,r]) := by
  constructor
  · intro r
    obtain ⟨x,hx,he⟩ := actual_primitive_horizontal_coordinate_surjective ht ha hc hX
      (show r+X 1 0 ∈ (univ : Set ℝ) from mem_univ _)
    have hline := actual_primitive_horizontal_line ht hX hx
    refine ⟨(x : ℂ),real_not_mem_rhombic_lattice_of_pos ht hx.1 hx.2,?_⟩
    ext j
    fin_cases j
    · change X (x : ℂ) 0-X 1 0 = r
      linarith
    · change X (x : ℂ) 1-X 1 1 = 0
      exact sub_eq_zero.mpr hline.1
    · change X (x : ℂ) 2-X 1 2 = 0
      exact sub_eq_zero.mpr hline.2
  · intro r
    obtain ⟨y,hy,he⟩ := actual_primitive_vertical_coordinate_surjective ht ha hc hX
      (show r+X 1 2 ∈ (univ : Set ℝ) from mem_univ _)
    have hline := actual_primitive_vertical_line ht hX hy
    refine ⟨1+I*y,rhombic_vertical_axis_not_mem ht hy,?_⟩
    ext j
    fin_cases j
    · change X (1+I*y) 0-X 1 0 = 0
      exact sub_eq_zero.mpr hline.1
    · change X (1+I*y) 1-X 1 1 = 0
      exact sub_eq_zero.mpr hline.2
    · change X (1+I*y) 2-X 1 2 = r
      linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_primitive_contains_complete_axes
