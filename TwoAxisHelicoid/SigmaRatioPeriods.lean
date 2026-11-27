import TwoAxisHelicoid.SigmaQuasiPeriods

namespace TwoAxisHelicoid
open Complex

noncomputable def sigmaRatio (s : ℂ → ℂ) (a z : ℂ) : ℂ :=
  s (z-a)*s (z+a)/(s z^2*s a^2)

theorem sigmaRatio_periodic_of_quasi (s : ℂ → ℂ) (a w c : ℂ)
    (hs : ∀ z, s (z+w) = -Complex.exp (c*(z+w/2))*s z) :
    Function.Periodic (sigmaRatio s a) w := by
  intro z
  have hm : z+w-a = (z-a)+w := by ring
  have hp : z+w+a = (z+a)+w := by ring
  have he : Complex.exp (c*(z-a+w/2))*Complex.exp (c*(z+a+w/2)) =
      Complex.exp (c*(z+w/2))^2 := by
    rw [← Complex.exp_add,← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  unfold sigmaRatio
  rw [hm,hp,hs,hs,hs]
  calc
    _ = (Complex.exp (c*(z-a+w/2))*Complex.exp (c*(z+a+w/2)))*(s (z-a)*s (z+a))/
        (Complex.exp (c*(z+w/2))^2*(s z^2*s a^2)) := by
      congr 1 <;> ring
    _ = Complex.exp (c*(z+w/2))^2*(s (z-a)*s (z+a))/
        (Complex.exp (c*(z+w/2))^2*(s z^2*s a^2)) := by rw [he]
    _ = _ := mul_div_mul_left _ _ (pow_ne_zero 2 (Complex.exp_ne_zero _))

theorem thetaSigmaRatio_period_two (t : ℝ) (a : ℂ) :
    Function.Periodic (sigmaRatio (thetaSigma t) a) 2 := by
  apply sigmaRatio_periodic_of_quasi _ _ _ (2*thetaEtaExpression t)
  intro z
  simpa using thetaSigma_add_two t z

theorem thetaSigmaRatio_period_half {t : ℝ} (ht : 0 < t) (a : ℂ) :
    Function.Periodic (sigmaRatio (thetaSigma t) a) (1+I*t) :=
  sigmaRatio_periodic_of_quasi _ _ _ (thetaEtaExpression t*(1+I*t)-Real.pi*I)
    (thetaSigma_add_half ht)

theorem thetaSigmaRatio_add_lattice {t : ℝ} (ht : 0 < t) (a z : ℂ)
    (l : (rhombicPeriodPair t ht).lattice) :
    sigmaRatio (thetaSigma t) a (z+l) = sigmaRatio (thetaSigma t) a z := by
  obtain ⟨m,n,he⟩ := PeriodPair.mem_lattice.mp l.property
  rw [← he]
  change sigmaRatio (thetaSigma t) a (z+((m:ℂ)*2+(n:ℂ)*(1+I*t))) = _
  have h1 := (thetaSigmaRatio_period_two t a).zsmul m z
  have h2 := (thetaSigmaRatio_period_half ht a).zsmul n (z+(m:ℂ)*2)
  simp only [zsmul_eq_mul] at h1 h2
  rw [← add_assoc,h2,h1]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaSigmaRatio_add_lattice
