import TwoAxisHelicoid.WeierstrassGeodesicFrame

namespace TwoAxisHelicoid
open Complex Real
set_option maxHeartbeats 1000000

/-- Differentiate the actual spatial velocity, including the parameter
acceleration term, along a twice differentiable parameter curve. -/
theorem weierstrass_velocity_curve_hasDerivAt
    {W : ℂ → ℂ} {z v : ℝ → ℂ} {D a : ℂ} {t : ℝ}
    (hW : HasDerivAt W D (z t)) (hz : HasDerivAt z (v t) t) (hv : HasDerivAt v a t) :
    HasDerivAt (fun s => nullRealDerivative (weierstrassTriple (exp (W (z s))) 1) (v s))
      (fun j => ((v t)^2*(D*weierstrassExpPrime (W (z t)) j)+
        a*weierstrassTriple (exp (W (z t))) 1 j).re) t := by
  have hΦ := weierstrass_exp_prime_hasDerivAt hW
  apply hasDerivAt_pi.mpr
  intro j
  have hΦj : HasDerivAt (fun w => weierstrassTriple (exp (W w)) 1 j)
      (D*weierstrassExpPrime (W (z t)) j) (z t) := hasDerivAt_pi.mp hΦ j
  have hc : HasDerivAt (fun s => weierstrassTriple (exp (W (z s))) 1 j)
      ((v t)*(D*weierstrassExpPrime (W (z t)) j)) t :=
    (hΦj.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hz
  have hp := hv.mul hc
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hp
  convert hr using 1
  · rfl
  · change ((v t)^2*(D*weierstrassExpPrime (W (z t)) j)+
      a*weierstrassTriple (exp (W (z t))) 1 j).re =
      (a*weierstrassTriple (exp (W (z t))) 1 j+
        v t*(v t*(D*weierstrassExpPrime (W (z t)) j))).re
    congr 1
    ring

theorem weierstrass_geodesic_velocity_hasDerivAt_normal
    {W : ℂ → ℂ} {z v : ℝ → ℂ} {D : ℂ} {t : ℝ}
    (hW : HasDerivAt W D (z t)) (hz : HasDerivAt z (v t) t)
    (hv : HasDerivAt v (-(logGaussConnection W (z t)*(v t)^2)) t) :
    HasDerivAt (fun s => nullRealDerivative (weierstrassTriple (exp (W (z s))) 1) (v s))
      (-(D*(v t)^2).re • logGaussSphere (W (z t)).re (W (z t)).im) t := by
  have h := weierstrass_velocity_curve_hasDerivAt hW hz hv
  convert h using 1
  funext j
  change -(D*(v t)^2).re*logGaussSphere (W (z t)).re (W (z t)).im j = _
  rw [logGaussConnection,hW.deriv]
  simpa only [sub_eq_add_neg,neg_mul] using
    (weierstrass_geodesic_acceleration_normal (W (z t)) D (v t) j).symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.weierstrass_geodesic_velocity_hasDerivAt_normal
