import TwoAxisHelicoid.HalfThetaWeights
import TwoAxisHelicoid.ExpEnclosure

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaJet thetaTerm

noncomputable def ellipticNome (t : ℝ) : ℝ := Real.exp (-Real.pi*t)

theorem ellipticNome_pos (t : ℝ) : 0 < ellipticNome t := Real.exp_pos _

theorem ellipticNome_le_quarter {t : ℝ} (ht : 1/2 ≤ t) : ellipticNome t ≤ 1/4 := by
  have harg : (3/2:ℝ) ≤ Real.pi*t := by nlinarith [Real.pi_gt_three]
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 3/2) 4
  norm_num [Finset.sum_range_succ] at he
  have hexp : (4:ℝ) ≤ Real.exp (Real.pi*t) := le_trans (by linarith) (Real.exp_le_exp.mpr harg)
  unfold ellipticNome
  rw [show -Real.pi*t = -(Real.pi*t) by ring,Real.exp_neg]
  rw [← one_div,div_le_iff₀ (Real.exp_pos _)]
  nlinarith

theorem thetaTriangular_exp (t : ℝ) (n : ℕ) :
    Real.exp (-Real.pi*t*n*(n+1)/2) = ellipticNome t^(thetaTriangular n) := by
  unfold ellipticNome
  rw [← Real.exp_nat_mul]
  congr 1
  rw [thetaTriangular_real]
  ring

theorem sin_odd_half_pi (n : ℕ) : Complex.sin ((2*n+1:ℂ)*(Real.pi/2)) = (-1:ℂ)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : ((2*(n+1:ℕ)+1:ℂ)*(Real.pi/2)) = (2*n+1)*(Real.pi/2)+Real.pi := by push_cast; ring
    rw [he,Complex.sin_add_pi,ih,pow_succ]
    ring

theorem thetaTerm_half_zero (t : ℝ) (n : ℕ) :
    thetaTerm t 0 n (Real.pi/2) = (halfThetaTerm halfWeightA (ellipticNome t) n:ℂ) := by
  have hs : thetaSign n = ((thetaSign n).re:ℂ) := by unfold thetaSign; split_ifs <;> simp
  simp only [thetaTerm,pow_zero,mul_one,sineJet_zero,sin_odd_half_pi,thetaTriangular_exp,
    halfThetaTerm,halfThetaSign,halfWeightA,mul_one]
  rw [hs]
  push_cast
  simp only [Complex.ofReal_re]
  ring

theorem thetaTerm_half_two (t : ℝ) (n : ℕ) :
    thetaTerm t 2 n (Real.pi/2) = -(halfThetaTerm halfWeightB (ellipticNome t) n:ℂ) := by
  rw [show 2 = 0+2 by rfl,thetaTerm_add_two,thetaTerm_half_zero]
  simp only [halfThetaTerm,halfWeightA,halfWeightB]
  push_cast
  ring

theorem thetaTerm_half_four (t : ℝ) (n : ℕ) :
    thetaTerm t 4 n (Real.pi/2) =
      ((halfThetaTerm halfWeightB (ellipticNome t) n+8*halfThetaTerm halfWeightJ (ellipticNome t) n:ℝ):ℂ) := by
  rw [show 4 = 2+2 by rfl,thetaTerm_add_two,thetaTerm_half_two]
  have he : (halfWeightB n:ℂ) = 8*(halfWeightE n:ℂ)+1 := by exact_mod_cast halfWeightB_eq n
  simp only [halfThetaTerm,halfWeightB,halfWeightJ,halfWeightE] at he ⊢
  push_cast at he ⊢
  linear_combination ((halfThetaSign n:ℂ)*(ellipticNome t:ℂ)^(thetaTriangular n)*(2*n+1)^2)*he

theorem thetaJet_half_zero (t : ℝ) :
    thetaJet t 0 (Real.pi/2) = (halfThetaSum halfWeightA (ellipticNome t):ℂ) := by
  simp only [thetaJet,thetaTerm_half_zero,halfThetaSum,Complex.ofReal_tsum]

theorem thetaJet_half_two (t : ℝ) :
    thetaJet t 2 (Real.pi/2) = -(halfThetaSum halfWeightB (ellipticNome t):ℂ) := by
  simp only [thetaJet,thetaTerm_half_two,halfThetaSum,tsum_neg,Complex.ofReal_tsum]

theorem thetaJet_half_four {t : ℝ} (ht : 1/2 ≤ t) :
    thetaJet t 4 (Real.pi/2) =
      ((halfThetaSum halfWeightB (ellipticNome t)+8*halfThetaSum halfWeightJ (ellipticNome t):ℝ):ℂ) := by
  have hq0 := (ellipticNome_pos t).le
  have hq := ellipticNome_le_quarter ht
  have hsB := (halfThetaB_tail hq0 hq).1
  have hsJ := (halfThetaJ_tail hq0 hq).1
  simp only [thetaJet,thetaTerm_half_four,halfThetaSum,← Complex.ofReal_tsum]
  rw [Summable.tsum_add hsB (hsJ.mul_left 8),tsum_mul_left]

theorem halfThetaB_sub_A {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1/4) :
    halfThetaSum halfWeightB q-halfThetaSum halfWeightA q = 8*halfThetaSum halfWeightE q := by
  have hA := (halfThetaA_tail hq0 hq).1
  have hB := (halfThetaB_tail hq0 hq).1
  unfold halfThetaSum
  rw [← hB.tsum_sub hA,← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold halfThetaTerm
  rw [halfWeightB_eq]
  simp only [halfWeightA]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaJet_half_four
