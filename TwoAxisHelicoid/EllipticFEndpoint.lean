import TwoAxisHelicoid.HalfThetaF
import TwoAxisHelicoid.HalfThetaSixTail
import TwoAxisHelicoid.VerticalEndpoint

namespace TwoAxisHelicoid

set_option maxRecDepth 10000

theorem halfThetaB_rational_bounds {q l u : ℝ} (hl0 : 0 ≤ l) (hl : l ≤ q)
    (hu : q ≤ u) (hu4 : u ≤ 1/4) :
    1-9*u-25*u^3+49*l^6+81*l^10-121*u^15-1/10^10 ≤ halfThetaSum halfWeightB q ∧
    halfThetaSum halfWeightB q ≤ 1-9*l-25*l^3+49*u^6+81*u^10-121*l^15+1/10^10 := by
  have hq0 : 0 ≤ q := hl0.trans hl
  have h := abs_le.mp (halfThetaB_six_error hq0 (hu.trans hu4))
  constructor
  · calc
      _ ≤ 1-9*q-25*q^3+49*q^6+81*q^10-121*q^15-1/10^10 := by gcongr
      _ ≤ halfThetaSum halfWeightB q := by linarith [h.1]
  · calc
      halfThetaSum halfWeightB q ≤ 1-9*q-25*q^3+49*q^6+81*q^10-121*q^15+1/10^10 := by linarith [h.2]
      _ ≤ _ := by gcongr

theorem halfThetaB_left_endpoint_neg :
    halfThetaSum halfWeightB (ellipticNome (70945978/100000000)) < 0 := by
  have h := (halfThetaB_rational_bounds (by norm_num : (0:ℝ) ≤ 10765392093268/100000000000000)
    nome_left_endpoint.1 nome_left_endpoint.2 (by norm_num)).2
  exact h.trans_lt (by norm_num)

theorem halfThetaB_right_endpoint_pos :
    0 < halfThetaSum halfWeightB (ellipticNome (70945980/100000000)) := by
  have h := (halfThetaB_rational_bounds (by norm_num : (0:ℝ) ≤ 10765391416858/100000000000000)
    nome_right_endpoint.1 nome_right_endpoint.2 (by norm_num)).1
  exact lt_of_lt_of_le (by norm_num) h

theorem ellipticFReal_left_endpoint_neg : ellipticFReal (70945978/100000000) < 0 := by
  rw [ellipticFReal_formula]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (by positivity) halfThetaB_left_endpoint_neg)
    (halfThetaSum_A_pos (ellipticNome_pos _).le (ellipticNome_le_quarter (by norm_num)))

theorem ellipticFReal_right_endpoint_pos : 0 < ellipticFReal (70945980/100000000) := by
  rw [ellipticFReal_formula]
  exact div_pos (mul_pos (by positivity) halfThetaB_right_endpoint_pos)
    (halfThetaSum_A_pos (ellipticNome_pos _).le (ellipticNome_le_quarter (by norm_num)))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ellipticFReal_left_endpoint_neg
#print axioms TwoAxisHelicoid.ellipticFReal_right_endpoint_pos
