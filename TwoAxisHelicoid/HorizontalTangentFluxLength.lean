import TwoAxisHelicoid.NullEuclideanMetric
import TwoAxisHelicoid.PiecewiseComplexPeriods
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped Manifold ENNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace

/-- The conjugate height on a tangent vector is bounded by the actual
Euclidean speed of the corresponding conformal immersion. -/
theorem abs_im_height_le_euclidean_velocity {p : Fin 3 → ℂ} (hp : ComplexNull p) (v : ℂ) :
    |(v*p 2).im| ≤ ‖coordinateToEuclidean (nullRealDerivative p v)‖ := by
  have h := PiLp.norm_apply_le (coordinateToEuclidean (nullRealDerivative p (I*v))) 2
  have he : (nullRealDerivative p (I*v)) 2 = -(v*p 2).im := by
    change (I*v*p 2).re = _
    rw [mul_assoc,I_mul_re]
  change ‖(nullRealDerivative p (I*v)) 2‖ ≤ _ at h
  rw [he,norm_neg,Real.norm_eq_abs] at h
  have hnorm : ‖coordinateToEuclidean (nullRealDerivative p (I*v))‖ =
      ‖coordinateToEuclidean (nullRealDerivative p v)‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [nullRealDerivative_euclidean_norm_sq hp,norm_mul,norm_I,one_mul]
  exact h.trans hnorm.le

/-- The inequality of Appendix B on a genuine C¹ arc, with mathlib's
extended Riemannian path length of the spatial parametrization. -/
theorem ComplexPeriodArc.height_flux_le_spatial_length {U : Set ℂ} (a : ComplexPeriodArc U)
    {X : ℂ → Fin 3 → ℝ} {p : ℂ → Fin 3 → ℂ}
    (hp : ∀ z ∈ U, ComplexNull (p z)) (hh : ContinuousOn (fun z => p z 2) U)
    (hX : ∀ z ∈ U, HasFDerivAt X (nullRealDerivative (p z)) z) :
    ‖(a.integral (fun z => p z 2)).im‖ₑ ≤ Manifold.pathELength 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      (coordinateToEuclidean ∘ X ∘ a.curve) a.left a.right := by
  have hi : IntervalIntegrable (fun s => a.velocity s*p (a.curve s) 2) volume a.left a.right := (a.continuous_velocity.mul (hh.comp a.continuous_curve a.stays)).intervalIntegrable_of_Icc a.ordered
  have e : (a.integral (fun z => p z 2)).im =
      ∫ s in a.left..a.right, (a.velocity s*p (a.curve s) 2).im :=
    (Complex.imCLM.intervalIntegral_comp_comm hi).symm
  rw [e,intervalIntegral.integral_of_le a.ordered,← restrict_Ioo_eq_restrict_Ioc,
    Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  apply (enorm_integral_le_lintegral_enorm _).trans
  apply setLIntegral_mono' measurableSet_Ioo
  intro s hs
  have hs' := a.stays (Ioo_subset_Icc_self hs)
  have hd := (coordinateToEuclidean.hasFDerivAt.comp _ (hX _ hs')).comp_hasDerivAt s (a.derivative s hs)
  rw [mfderiv_eq_fderiv]
  change ‖(a.velocity s*p (a.curve s) 2).im‖ₑ ≤
    ‖fderiv ℝ ((coordinateToEuclidean ∘ X) ∘ a.curve) s 1‖ₑ
  rw [hd.hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.toSpanSingleton_apply,one_smul,ContinuousLinearMap.comp_apply]
  change ‖(a.velocity s*p (a.curve s) 2).im‖ₑ ≤ ‖coordinateToEuclidean (nullRealDerivative (p (a.curve s)) (a.velocity s))‖ₑ
  rw [← ofReal_norm,← ofReal_norm,Real.norm_eq_abs]
  exact ENNReal.ofReal_le_ofReal (abs_im_height_le_euclidean_velocity (hp _ hs') (a.velocity s))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.ComplexPeriodArc.height_flux_le_spatial_length
