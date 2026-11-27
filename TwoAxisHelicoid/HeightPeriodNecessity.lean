import TwoAxisHelicoid.RealPrimitivePeriods
import TwoAxisHelicoid.EllipticRealNormalization

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped Interval

theorem actual_height_primitive_sloping_period_zero {t : ℝ} (ht : 0 < t)
    {f : ℂ → ℂ} {F : ℂ → ℝ}
    (hf : ∀ z ∉ (rhombicPeriodPair t ht).lattice, DifferentiableAt ℂ f z)
    (hF : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      HasFDerivAt F (realCoefficientDerivative (f z)) z)
    (hp : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      ∀ ω ∈ (rhombicPeriodPair t ht).lattice, F (z+ω) = F z) :
    (ellipticLinePeriod f (-1) (1+I*t)).re = 0 := by
  let path : ℝ → ℂ := fun s => -1+(s : ℂ)*(1+I*t)
  have hpath (s : ℝ) : HasDerivAt path (1+I*t) s := by
    simpa only [path,id_eq,Complex.ofReal_one,one_mul] using
      ((((hasDerivAt_id s).ofReal_comp).mul_const (1+I*t)).const_add (-1))
  have hreg (s : ℝ) : path s ∉ (rhombicPeriodPair t ht).lattice := rhombic_sloping_line_not_mem ht s
  have hI : IntervalIntegrable (fun s => f (path s)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro s _
    exact ((hf _ (hreg s)).continuousAt.comp (hpath s).continuousAt).continuousWithinAt
  have he := real_primitive_path_integral_eq_sub (a := 0) (b := 1)
    (fun s _ => hpath s) (fun s _ => hF _ (hreg s)) hI
  have hper := hp (-1) (by simpa [path] using hreg 0) (1+I*t) (rhombicPeriodPair t ht).ω₂_mem_lattice
  simp only [path,Complex.ofReal_zero,Complex.ofReal_one,zero_mul,one_mul,add_zero] at he
  rw [hper,sub_self] at he
  simpa only [ellipticLinePeriod,intervalIntegral.integral_const_mul,path] using he

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_height_primitive_sloping_period_zero
