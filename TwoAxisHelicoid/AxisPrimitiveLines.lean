import TwoAxisHelicoid.AxisCoordinateDifferentials
import TwoAxisHelicoid.RealPrimitivePeriods

namespace TwoAxisHelicoid
open Complex Set

theorem actual_primitive_horizontal_hasDerivAt {t a c x : ℝ} (ht : 0 < t)
    {X : ℂ → Fin 3 → ℝ} (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (hx : x ∈ Ioo (0 : ℝ) 2) (j : Fin 3) :
    HasDerivAt (fun u : ℝ => X (u : ℂ) j) (coordinateData t a c ht x j).re x := by
  have hz := real_not_mem_rhombic_lattice_of_pos ht hx.1 hx.2
  have h := (actual_coordinate_primitive_component ht hX hz j).comp_hasDerivAt x
    (hasDerivAt_id x).ofReal_comp
  simpa only [realCoefficientDerivative_apply,Complex.ofReal_one,one_mul,Function.comp_def,id_eq] using h

theorem actual_primitive_vertical_hasDerivAt {t a c y : ℝ} (ht : 0 < t)
    {X : ℂ → Fin 3 → ℝ} (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (hy : y ∈ Ioo (-t) t) (j : Fin 3) :
    HasDerivAt (fun u : ℝ => X (1+I*u) j) (I*coordinateData t a c ht (1+I*y) j).re y := by
  have hz := rhombic_vertical_axis_not_mem ht hy
  have hp : HasDerivAt (fun u : ℝ => (1 : ℂ)+I*u) I y := by
    convert (((hasDerivAt_id y).ofReal_comp).const_mul I).const_add (1 : ℂ) using 1
    · rfl
    · simp
  exact (actual_coordinate_primitive_component ht hX hz j).comp_hasDerivAt y hp

theorem actual_primitive_horizontal_line {t a c x : ℝ} (ht : 0 < t)
    {X : ℂ → Fin 3 → ℝ} (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (hx : x ∈ Ioo (0 : ℝ) 2) :
    X (x : ℂ) 1 = X 1 1 ∧ X (x : ℂ) 2 = X 1 2 := by
  have he (j : Fin 3) (hj : ∀ u ∈ Ioo (0 : ℝ) 2, (coordinateData t a c ht u j).re = 0) :
      X (x : ℂ) j = X 1 j := by
    apply isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0 : ℝ) 2).isPreconnected
      (fun u hu => (actual_primitive_horizontal_hasDerivAt ht hX hu j).differentiableAt.differentiableWithinAt)
      ?_ hx (by norm_num : (1 : ℝ) ∈ Ioo (0 : ℝ) 2)
    intro u hu
    change deriv (fun v : ℝ => X (v : ℂ) j) u = 0
    rw [(actual_primitive_horizontal_hasDerivAt ht hX hu j).deriv,hj u hu]
  exact ⟨he 1 (fun u _ => (coordinateData_horizontal_axis (a := a) (c := c) ht u).1),
    he 2 (fun u _ => (coordinateData_horizontal_axis (a := a) (c := c) ht u).2)⟩

theorem actual_primitive_vertical_line {t a c y : ℝ} (ht : 0 < t)
    {X : ℂ → Fin 3 → ℝ} (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (hy : y ∈ Ioo (-t) t) :
    X (1+I*y) 0 = X 1 0 ∧ X (1+I*y) 1 = X 1 1 := by
  have he (j : Fin 3) (hj : ∀ u ∈ Ioo (-t) t, (I*coordinateData t a c ht (1+I*u) j).re = 0) :
      X (1+I*y) j = X 1 j := by
    have heq : X (1+I*y) j = X (1+I*(0 : ℝ)) j := by
      apply isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-t) t).isPreconnected
        (fun u hu => (actual_primitive_vertical_hasDerivAt ht hX hu j).differentiableAt.differentiableWithinAt)
        ?_ hy (by constructor <;> linarith : (0 : ℝ) ∈ Ioo (-t) t)
      intro u hu
      change deriv (fun v : ℝ => X (1+I*v) j) u = 0
      rw [(actual_primitive_vertical_hasDerivAt ht hX hu j).deriv,hj u hu]
    simpa only [Complex.ofReal_zero,mul_zero,add_zero] using heq
  constructor
  · apply he 0
    intro u _
    simp [Complex.mul_re,(coordinateData_vertical_axis (a := a) (c := c) ht u).1]
  · apply he 1
    intro u _
    simp [Complex.mul_re,(coordinateData_vertical_axis (a := a) (c := c) ht u).2]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_primitive_horizontal_line
#print axioms TwoAxisHelicoid.actual_primitive_vertical_line
