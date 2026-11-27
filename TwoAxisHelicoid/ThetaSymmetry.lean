import TwoAxisHelicoid.ThetaPeriod

/-! Periodicity and reality of the concrete theta functions. -/

namespace TwoAxisHelicoid
open Complex
open scoped ComplexConjugate

theorem sineJet_add_pi (j : ℕ) (v : ℂ) :
    sineJet j (v+Real.pi) = -sineJet j v := by
  induction j using Nat.twoStepInduction with
  | zero => simp only [sineJet_zero, Complex.sin_add_pi]
  | one => simp only [sineJet_one, Complex.cos_add_pi]
  | more j hj _ => rw [sineJet_add_two, sineJet_add_two, hj]

theorem sineJet_add_nat_two_pi (j n : ℕ) (v : ℂ) :
    sineJet j (v+n*(2*Real.pi)) = sineJet j v := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : v+(n+1 : ℕ)*(2*Real.pi) = ((v+n*(2*Real.pi))+Real.pi)+Real.pi := by
      push_cast
      ring
    rw [he, sineJet_add_pi, sineJet_add_pi, neg_neg, ih]

theorem thetaTerm_add_pi (t : ℝ) (j n : ℕ) (v : ℂ) :
    thetaTerm t j n (v+Real.pi) = -thetaTerm t j n v := by
  have he : (2*n+1 : ℂ)*(v+Real.pi) = ((2*n+1)*v+n*(2*Real.pi))+Real.pi := by ring
  simp only [thetaTerm, he, sineJet_add_pi, sineJet_add_nat_two_pi]
  ring

theorem thetaJet_add_pi (t : ℝ) (j : ℕ) (v : ℂ) :
    thetaJet t j (v+Real.pi) = -thetaJet t j v := by
  simp only [thetaJet, thetaTerm_add_pi, tsum_neg]

theorem thetaQuotient_add_pi (t : ℝ) (j : ℕ) (v : ℂ) :
    thetaQuotient t j (v+Real.pi) = thetaQuotient t j v := by
  simp [thetaQuotient, thetaJet_add_pi]

theorem thetaA_periodic (t a : ℝ) : Function.Periodic (thetaA t a) 2 := by
  intro z
  have h1 : (Real.pi*(z+2-a)/2 : ℂ) = Real.pi*(z-a)/2+Real.pi := by ring
  have h2 : (Real.pi*(z+2)/2 : ℂ) = Real.pi*z/2+Real.pi := by ring
  simp [thetaA, h1, h2, thetaJet_add_pi, thetaQuotient_add_pi]

theorem sineJet_conj (j : ℕ) (v : ℂ) : sineJet j (conj v) = conj (sineJet j v) := by
  induction j using Nat.twoStepInduction with
  | zero => simp only [sineJet_zero, Complex.sin_conj]
  | one => simp only [sineJet_one, Complex.cos_conj]
  | more j hj _ => simp only [sineJet_add_two, hj, map_neg]

theorem thetaTerm_conj (t : ℝ) (j n : ℕ) (v : ℂ) :
    thetaTerm t j n (conj v) = conj (thetaTerm t j n v) := by
  have hs : conj (thetaSign n) = thetaSign n := by unfold thetaSign; split <;> simp
  have hc2 : conj (2 : ℂ) = 2 := Complex.conj_ofReal 2
  have harg : (2*n+1 : ℂ)*conj v = conj ((2*n+1 : ℂ)*v) := by simp [hc2]
  unfold thetaTerm
  rw [harg, sineJet_conj]
  simp only [map_mul, hs, Complex.conj_ofReal,
    map_pow, map_add, map_one, map_ofNat, map_natCast]

theorem thetaJet_conj (t : ℝ) (j : ℕ) (v : ℂ) :
    thetaJet t j (conj v) = conj (thetaJet t j v) := by
  simp only [thetaJet, thetaTerm_conj]
  exact Complex.conjCLE.map_tsum.symm

theorem thetaJet_real (t : ℝ) (j : ℕ) (x : ℝ) :
    (thetaJet t j x).im = 0 := by
  have h := thetaJet_conj t j (x : ℂ)
  simp only [Complex.conj_ofReal] at h
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith

theorem thetaG_real (t a : ℝ) : (thetaG t a).im = 0 := by
  have hv : (Real.pi*a/2 : ℂ) = ((Real.pi*a/2 : ℝ) : ℂ) := by push_cast; rfl
  have h0 := thetaJet_real t 0 (Real.pi*a/2)
  have h1 := thetaJet_real t 1 (Real.pi*a/2)
  have h2 := thetaJet_real t 2 (Real.pi*a/2)
  rw [← hv] at h0 h1 h2
  simp [thetaG, thetaQuotient, Complex.div_im, Complex.mul_im, h0, h1, h2, pow_two]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaA_periodic
#print axioms TwoAxisHelicoid.thetaG_real
