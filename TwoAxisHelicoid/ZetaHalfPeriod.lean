import TwoAxisHelicoid.ThetaSigmaZeta

namespace TwoAxisHelicoid
open Complex
open scoped ComplexConjugate
attribute [local irreducible] thetaJet thetaScaledJet

theorem thetaJet_one_half_pi (t : ℝ) : thetaJet t 1 (Real.pi/2) = 0 := by
  have hc (n : ℕ) : sineJet 1 ((2*n+1:ℂ)*(Real.pi/2)) = 0 := by
    induction n with
    | zero => simp [sineJet_one]
    | succ n ih =>
      have he : ((2*(n+1)+1:ℂ)*(Real.pi/2)) = (2*n+1)*(Real.pi/2)+Real.pi := by ring
      simp only [Nat.cast_add,Nat.cast_one]
      rw [he,sineJet_add_pi,ih,neg_zero]
  have hn (n : ℕ) : thetaTerm t 1 n (Real.pi/2) = 0 := by simp only [thetaTerm,hc,mul_zero]
  simp only [thetaJet,hn,tsum_zero]

theorem thetaZeta_one (t : ℝ) : thetaZeta t 1 = thetaEtaExpression t := by
  have hf : thetaScaledJet t 1 1 = 0 := by
    simp only [thetaScaledJet,pow_one,mul_one,thetaJet_one_half_pi,mul_zero]
  simp only [thetaZeta,hf,zero_div,mul_one,zero_add]

theorem thetaScaledJet_conj (t : ℝ) (j : ℕ) (z : ℂ) :
    thetaScaledJet t j (conj z) = conj (thetaScaledJet t j z) := by
  have hc2 : conj (2:ℂ) = 2 := Complex.conj_ofReal 2
  have hc : conj (Real.pi/2:ℂ) = (Real.pi/2:ℂ) := by
    simp only [map_div₀,Complex.conj_ofReal,hc2]
  have hz : (Real.pi/2:ℂ)*conj z = conj ((Real.pi/2:ℂ)*z) := by simp only [map_mul,hc]
  unfold thetaScaledJet
  rw [hz,thetaJet_conj]
  simp only [map_mul,map_pow,hc]

theorem thetaEtaExpression_conj (t : ℝ) : conj (thetaEtaExpression t) = thetaEtaExpression t := by
  have hj (j : ℕ) : conj (thetaScaledJet t j 0) = thetaScaledJet t j 0 := by
    simpa using (thetaScaledJet_conj t j 0).symm
  have hc3 : conj (3:ℂ) = 3 := Complex.conj_ofReal 3
  simp only [thetaEtaExpression,map_neg,map_div₀,map_mul,hc3,hj]

theorem thetaEtaExpression_real (t : ℝ) : (thetaEtaExpression t).im = 0 := by
  have h := congrArg Complex.im (thetaEtaExpression_conj t)
  simp only [Complex.conj_im] at h
  linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaZeta_one
