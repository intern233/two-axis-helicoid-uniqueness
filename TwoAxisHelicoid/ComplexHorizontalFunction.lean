import TwoAxisHelicoid.ComplexThetaC1
import TwoAxisHelicoid.ComplexVerticalFunction

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] complexThetaJet thetaJet

noncomputable def complexA (t a z : ℂ) : ℂ :=
  ((Real.pi*complexThetaJet t 1 0)/(2*complexThetaJet t 0 (Real.pi*a/2)))^2*
    (complexThetaJet t 0 (Real.pi*(z-a)/2)/complexThetaJet t 0 (Real.pi*z/2))^2*
    Complex.exp ((a-1)*Real.pi*complexThetaQuotient t 1 (Real.pi*z/2))

theorem complexA_ofReal (t a : ℝ) (z : ℂ) : complexA t a z = thetaA t a z := by
  simp only [complexA,thetaA,complexThetaJet_ofReal,complexThetaQuotient_ofReal]

theorem complexA_contDiffAt_one {t a z : ℂ} (ht : 0 < t.re)
    (ha : complexThetaJet t 0 (Real.pi*a/2) ≠ 0)
    (hz : complexThetaJet t 0 (Real.pi*z/2) ≠ 0) :
    ContDiffAt ℂ 1 (fun p : ℂ × ℂ × ℂ => complexA p.1 p.2.1 p.2.2) (t,a,z) := by
  have htheta (j : ℕ) (v : ℂ × ℂ × ℂ → ℂ) (hv : ContDiffAt ℂ 1 v (t,a,z)) :
      ContDiffAt ℂ 1 (fun p : ℂ × ℂ × ℂ => complexThetaJet p.1 j (v p)) (t,a,z) := by
    have h := (complexThetaJet_contDiffAt_one ht j (v (t,a,z))).comp (t,a,z)
      (contDiffAt_fst.prodMk hv)
    exact h
  have hzero := htheta 1 (fun _ => 0) contDiffAt_const
  have ha0 := htheta 0 (fun p => Real.pi*p.2.1/2) (by fun_prop)
  have hz0 := htheta 0 (fun p => Real.pi*p.2.2/2) (by fun_prop)
  have hz1 := htheta 1 (fun p => Real.pi*p.2.2/2) (by fun_prop)
  have hm := htheta 0 (fun p => Real.pi*(p.2.2-p.2.1)/2) (by fun_prop)
  have hc : ContDiffAt ℂ 1 (fun p : ℂ × ℂ × ℂ =>
      ((Real.pi*complexThetaJet p.1 1 0)/(2*complexThetaJet p.1 0 (Real.pi*p.2.1/2)))^2) (t,a,z) :=
    ((contDiffAt_const.mul hzero).div (contDiffAt_const.mul ha0)
    (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) ha)).pow 2
  have hr := (hm.div hz0 hz).pow 2
  have hcoef : ContDiffAt ℂ 1 (fun p : ℂ × ℂ × ℂ => (p.2.1-1)*Real.pi) (t,a,z) := by fun_prop
  have he := (hcoef.mul (hz1.div hz0 hz)).cexp
  unfold complexA complexThetaQuotient
  exact (hc.mul hr).mul he

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.complexA_contDiffAt_one
