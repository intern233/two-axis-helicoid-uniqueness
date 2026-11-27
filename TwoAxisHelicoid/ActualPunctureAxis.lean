import TwoAxisHelicoid.AxisPrimitiveLines

namespace TwoAxisHelicoid
open Complex Set

/-- Periodicity joins the two vertical rays next to the puncture to the
same actual vertical axis through the marked point. -/
theorem actual_periodic_primitive_puncture_axis {t a c s : ℝ} (ht : 0 < t)
    {X : ℂ → Fin 3 → ℝ} (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (hp : ∀ z ω : ℂ, ω ∈ (rhombicPeriodPair t ht).lattice → X (z+ω) = X z)
    (hs0 : s ≠ 0) (hs : |s| < t) :
    X (I*s) 0 = X 1 0 ∧ X (I*s) 1 = X 1 1 := by
  rcases lt_or_gt_of_ne hs0 with hn | hpos
  · have hy : s+t ∈ Ioo (-t) t := by
      have hh := (abs_lt.mp hs).1
      constructor <;> linarith
    have he := hp (I*s) (1+I*t) (rhombicPeriodPair t ht).ω₂_mem_lattice
    rw [show I*(s : ℂ)+(1+I*(t : ℂ)) = 1+I*((s+t : ℝ) : ℂ) by push_cast; ring] at he
    rw [← he]
    exact actual_primitive_vertical_line ht hX hy
  · have hy : s-t ∈ Ioo (-t) t := by
      have hh := (abs_lt.mp hs).2
      constructor <;> linarith
    have hω : (1-I*(t : ℂ)) ∈ (rhombicPeriodPair t ht).lattice := by
      have hh := (rhombicPeriodPair t ht).lattice.sub_mem
        (rhombicPeriodPair t ht).ω₁_mem_lattice (rhombicPeriodPair t ht).ω₂_mem_lattice
      convert hh using 1
      dsimp [rhombicPeriodPair]
      ring
    have he := hp (I*s) (1-I*t) hω
    rw [show I*(s : ℂ)+(1-I*(t : ℂ)) = 1+I*((s-t : ℝ) : ℂ) by push_cast; ring] at he
    rw [← he]
    exact actual_primitive_vertical_line ht hX hy

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_periodic_primitive_puncture_axis
