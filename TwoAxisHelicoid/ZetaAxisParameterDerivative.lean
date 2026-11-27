import TwoAxisHelicoid.ZetaAxisEndpointLimits

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- The parameter derivative of the manuscript's actual axis integral.
The previously proved exact contour formula justifies it on the entire
open parameter interval, without an unproved exchange of limits. -/
theorem thetaZeta_axis_integral_hasDerivAt {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun u : ℝ => I*(∫ y : ℝ in 0..2*t, zetaAxisDifference t u y))
      (-2*zetaImaginaryQuasi t) a := by
  have hd := ((((hasDerivAt_id a).ofReal_comp.const_mul (-2 : ℂ)).mul_const
    (zetaImaginaryQuasi t)).sub_const (2*(Real.pi : ℂ)*I))
  have he : (fun u : ℝ => I*(∫ y : ℝ in 0..2*t, zetaAxisDifference t u y)) =ᶠ[𝓝 a]
      (fun u : ℝ => -2*(u : ℂ)*zetaImaginaryQuasi t-2*(Real.pi : ℂ)*I) := by
    filter_upwards [isOpen_Ioo.mem_nhds ha] with u hu
    exact thetaZeta_axis_difference_integral ht hu
  simpa only [id_eq,Complex.ofReal_one,mul_one] using! hd.congr_of_eventuallyEq he

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaZeta_axis_integral_hasDerivAt
