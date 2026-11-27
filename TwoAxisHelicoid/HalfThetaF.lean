import TwoAxisHelicoid.HalfThetaIdentity
import TwoAxisHelicoid.HalfThetaDeterminant
import TwoAxisHelicoid.EllipticFReciprocal

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaJet thetaLogSecond

noncomputable def ellipticFReal (t : ℝ) : ℝ := (thetaLogSecond t 1).re

theorem ellipticF_eq_ellipticFReal {t : ℝ} (ht : 0 < t) : ellipticF t ht = ellipticFReal t := by
  have he := thetaLogSecond_eq_weierstrassP_add_eta_of_pos ht ht
    (real_not_mem_rhombic_lattice_of_pos ht (by norm_num : (0:ℝ) < 1) (by norm_num : (1:ℝ) < 2))
  unfold ellipticF ellipticFReal
  simpa only [Complex.ofReal_one,add_comm] using (congrArg Complex.re he).symm

theorem thetaLogSecond_one_half_series (t : ℝ) :
    thetaLogSecond t 1 = ((Real.pi^2/4*halfThetaSum halfWeightB (ellipticNome t)/
      halfThetaSum halfWeightA (ellipticNome t):ℝ):ℂ) := by
  simp only [thetaLogSecond,mul_one,thetaQuotient,thetaJet_one_half_pi,zero_div,
    zero_pow (by decide : (2:ℕ) ≠ 0),thetaJet_half_two,thetaJet_half_zero]
  push_cast
  ring

theorem ellipticFReal_formula (t : ℝ) :
    ellipticFReal t = Real.pi^2/4*halfThetaSum halfWeightB (ellipticNome t)/
      halfThetaSum halfWeightA (ellipticNome t) := by
  unfold ellipticFReal
  rw [thetaLogSecond_one_half_series,Complex.ofReal_re]

theorem halfThetaA_parameter_hasDerivAt {t : ℝ} (ht : 1/2 ≤ t) :
    HasDerivAt (fun s => halfThetaSum halfWeightA (ellipticNome s))
      (-Real.pi*halfThetaSum halfWeightE (ellipticNome t)) t := by
  have ht0 : 0 < t := by linarith
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (thetaJet_parameter_hasDerivAt ht0 0 (Real.pi/2))
  convert hd using 1
  · funext s
    change halfThetaSum halfWeightA (ellipticNome s) = (thetaJet s 0 (Real.pi/2)).re
    rw [thetaJet_half_zero]
    rfl
  · rw [thetaJet_half_two,thetaJet_half_zero]
    have he := halfThetaB_sub_A (ellipticNome_pos t).le (ellipticNome_le_quarter ht)
    norm_num [Complex.mul_re,Complex.mul_im,Complex.div_ofNat_re,Complex.div_ofNat_im]
    linear_combination (Real.pi/8)*he

theorem halfThetaB_parameter_hasDerivAt {t : ℝ} (ht : 1/2 ≤ t) :
    HasDerivAt (fun s => halfThetaSum halfWeightB (ellipticNome s))
      (-Real.pi*halfThetaSum halfWeightJ (ellipticNome t)) t := by
  have ht0 : 0 < t := by linarith
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (thetaJet_parameter_hasDerivAt ht0 2 (Real.pi/2)).neg
  convert hd using 1
  · funext s
    change halfThetaSum halfWeightB (ellipticNome s) = (-thetaJet s 2 (Real.pi/2)).re
    rw [thetaJet_half_two]
    simp
  · rw [thetaJet_half_four ht,thetaJet_half_two]
    norm_num [Complex.mul_re,Complex.mul_im,Complex.div_ofNat_re,Complex.div_ofNat_im]
    ring

theorem ellipticFReal_hasDerivAt {t : ℝ} (ht : 1/2 ≤ t) :
    HasDerivAt ellipticFReal
      (Real.pi^3/4*(halfThetaSum halfWeightB (ellipticNome t)*halfThetaSum halfWeightE (ellipticNome t)-
        halfThetaSum halfWeightA (ellipticNome t)*halfThetaSum halfWeightJ (ellipticNome t))/
          (halfThetaSum halfWeightA (ellipticNome t))^2) t := by
  have ha := halfThetaSum_A_pos (ellipticNome_pos t).le (ellipticNome_le_quarter ht)
  have hd := ((halfThetaB_parameter_hasDerivAt ht).div (halfThetaA_parameter_hasDerivAt ht) ha.ne').const_mul (Real.pi^2/4)
  convert hd using 1
  · funext s
    simp only [Pi.div_apply]
    rw [ellipticFReal_formula]
    ring
  · ring

theorem ellipticFReal_deriv_pos {t : ℝ} (ht : 1/2 ≤ t) : 0 < deriv ellipticFReal t := by
  rw [(ellipticFReal_hasDerivAt ht).deriv]
  exact div_pos (mul_pos (by positivity)
    (halfThetaSum_determinant_pos (ellipticNome_pos t) (ellipticNome_le_quarter ht)))
      (pow_pos (halfThetaSum_A_pos (ellipticNome_pos t).le (ellipticNome_le_quarter ht)) 2)

theorem ellipticFReal_strictMono : StrictMonoOn ellipticFReal (Ici (1/2:ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro t ht
    exact (ellipticFReal_hasDerivAt ht).continuousAt.continuousWithinAt
  · intro t ht
    exact ellipticFReal_deriv_pos (interior_subset ht)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ellipticFReal_strictMono
