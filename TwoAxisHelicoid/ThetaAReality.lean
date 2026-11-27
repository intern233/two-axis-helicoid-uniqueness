import TwoAxisHelicoid.ThetaSymmetry

namespace TwoAxisHelicoid
open Complex
open scoped ComplexConjugate
attribute [local irreducible] thetaJet thetaQuotient thetaTerm

theorem thetaQuotient_conj (t : ℝ) (j : ℕ) (v : ℂ) :
    thetaQuotient t j (conj v) = conj (thetaQuotient t j v) := by
  simp only [thetaQuotient, thetaJet_conj, map_div₀]

theorem thetaA_conj (t a : ℝ) (z : ℂ) : thetaA t a (conj z) = conj (thetaA t a z) := by
  have h2 : conj (2 : ℂ) = 2 := Complex.conj_ofReal 2
  have hm : (Real.pi*(conj z-a)/2 : ℂ) = conj (Real.pi*(z-a)/2) := by simp [h2]
  have hz : (Real.pi*conj z/2 : ℂ) = conj (Real.pi*z/2) := by simp [h2]
  have ha : (Real.pi*a/2 : ℂ) = conj (Real.pi*a/2 : ℂ) := by simp [h2]
  have h0 : thetaJet t 1 0 = conj (thetaJet t 1 0) := by
    simpa using thetaJet_conj t 1 (0 : ℂ)
  have hsa : thetaJet t 0 (Real.pi*a/2) = conj (thetaJet t 0 (Real.pi*a/2)) := by
    simpa only [← ha] using thetaJet_conj t 0 (Real.pi*a/2)
  unfold thetaA
  rw [hm, hz]
  simp only [thetaJet_conj, thetaQuotient_conj]
  simp only [map_mul, map_div₀,
    map_pow, map_sub, map_one, h2, Complex.conj_ofReal, ← Complex.exp_conj]
  rw [← h0, ← hsa]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaA_conj
