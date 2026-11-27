import TwoAxisHelicoid.GaussKernelIdentity

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaSigma thetaZeta

theorem gauss_multiplier_algebra (a m eta z w k Z sm sp : ℂ) :
    I*Complex.exp (2*(a-m)*(Z+k)+2*m*eta*(z+w))*(-Complex.exp (k*(z-a+w/2))*sm)/
      (-Complex.exp (k*(z+a+w/2))*sp) =
    Complex.exp (2*m*(eta*w-k))*(I*Complex.exp (2*(a-m)*Z+2*m*eta*z)*sm/sp) := by
  have he : Complex.exp (2*(a-m)*(Z+k)+2*m*eta*(z+w))*Complex.exp (k*(z-a+w/2)) =
      Complex.exp (k*(z+a+w/2))*(Complex.exp (2*m*(eta*w-k))*
        Complex.exp (2*(a-m)*Z+2*m*eta*z)) := by
    simp only [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = (Complex.exp (2*(a-m)*(Z+k)+2*m*eta*(z+w))*Complex.exp (k*(z-a+w/2)))*
        (I*sm)/(Complex.exp (k*(z+a+w/2))*sp) := by ring
    _ = Complex.exp (k*(z+a+w/2))*
        (Complex.exp (2*m*(eta*w-k))*Complex.exp (2*(a-m)*Z+2*m*eta*z)*(I*sm))/
        (Complex.exp (k*(z+a+w/2))*sp) := by rw [he]; congr 1; ring
    _ = Complex.exp (2*m*(eta*w-k))*Complex.exp (2*(a-m)*Z+2*m*eta*z)*(I*sm)/sp :=
      mul_div_mul_left _ _ (Complex.exp_ne_zero _)
    _ = _ := by ring

theorem thetaGauss_quasiperiod {t a : ℝ} (m : ℤ) {z w k : ℂ}
    (hs : ∀ v, thetaSigma t (v+w) = -Complex.exp (k*(v+w/2))*thetaSigma t v)
    (hz : thetaZeta t (z+w) = thetaZeta t z+k) :
    thetaGauss t a m (z+w) = Complex.exp (2*m*(thetaEtaExpression t*w-k))*thetaGauss t a m z := by
  have hm : z+w-a = (z-a)+w := by ring
  have hp : z+w+a = (z+a)+w := by ring
  unfold thetaGauss
  rw [hm,hp,hs,hs,hz]
  exact gauss_multiplier_algebra _ _ _ _ _ _ _ _ _

theorem thetaGauss_period_two (t a : ℝ) (m : ℤ) : Function.Periodic (thetaGauss t a m) 2 := by
  intro z
  have h := thetaGauss_quasiperiod (t := t) (a := a) m (z := z) (w := 2) (k := 2*thetaEtaExpression t)
    (fun v => by simpa using thetaSigma_add_two t v) (thetaZeta_add_two t z)
  simpa only [mul_comm (thetaEtaExpression t) 2,sub_self,mul_zero,Complex.exp_zero,one_mul] using h

theorem thetaGauss_period_half {t a : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) (m : ℤ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht0).lattice) :
    thetaGauss t a m (z+(1+I*t)) = thetaGauss t a m z := by
  have h := thetaGauss_quasiperiod (t := t) (a := a) m (z := z)
    (w := 1+I*t) (k := thetaEtaExpression t*(1+I*t)-Real.pi*I)
    (thetaSigma_add_half ht0) (by simpa only [add_sub_assoc] using thetaZeta_add_half ht ht0 hz)
  have he : (2*(m:ℂ)*(thetaEtaExpression t*(1+I*t)-
      (thetaEtaExpression t*(1+I*t)-Real.pi*I))) = (m:ℂ)*(2*Real.pi*I) := by ring
  rw [he,Complex.exp_int_mul,Complex.exp_two_pi_mul_I,one_zpow,one_mul] at h
  exact h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaGauss_period_half
