import TwoAxisHelicoid.HalfThetaWeights

namespace TwoAxisHelicoid

theorem halfThetaDeterminant_pos {q A B E J : ℝ} (hq0 : 0 < q) (hq : q ≤ 1/4)
    (hA : |A-(1-q)| ≤ 2*q^3) (hB : |B-(1-9*q)| ≤ 26*q^3)
    (hE : |E-(-q)| ≤ 4*q^3) (hJ : |J-(-9*q)| ≤ 80*q^3) : 0 < B*E-A*J := by
  let rA := A-(1-q)
  let rB := B-(1-9*q)
  let rE := E-(-q)
  let rJ := J-(-9*q)
  have ha0 : |1-q| ≤ (1:ℝ) := abs_le.mpr ⟨by linarith,by linarith⟩
  have hb0 : |1-9*q| ≤ (5/4:ℝ) := abs_le.mpr ⟨by linarith,by linarith⟩
  have herr : |B*E-A*J-8*q| ≤ 85*q^3+44*q^4+264*q^6 := by
    calc
      |B*E-A*J-8*q| = |(1-9*q)*rE+(-q*rB)+rB*rE+(-(1-q)*rJ)+(9*q*rA)+(-rA*rJ)| := by
        congr 1
        dsimp [rA,rB,rE,rJ]
        ring
      _ ≤ |(1-9*q)*rE|+|-q*rB|+|rB*rE|+|-(1-q)*rJ|+|9*q*rA|+|-rA*rJ| := by
        calc
          _ ≤ |(1-9*q)*rE+(-q*rB)+rB*rE+(-(1-q)*rJ)+(9*q*rA)|+|-rA*rJ| := abs_add_le _ _
          _ ≤ (|(1-9*q)*rE+(-q*rB)+rB*rE+(-(1-q)*rJ)|+|9*q*rA|)+|-rA*rJ| := by gcongr; exact abs_add_le _ _
          _ ≤ ((|(1-9*q)*rE+(-q*rB)+rB*rE|+|-(1-q)*rJ|)+|9*q*rA|)+|-rA*rJ| := by gcongr; exact abs_add_le _ _
          _ ≤ (((|(1-9*q)*rE+(-q*rB)|+|rB*rE|)+|-(1-q)*rJ|)+|9*q*rA|)+|-rA*rJ| := by gcongr; exact abs_add_le _ _
          _ ≤ _ := by gcongr; exact abs_add_le _ _
      _ ≤ (5/4)*(4*q^3)+q*(26*q^3)+(26*q^3)*(4*q^3)+
          1*(80*q^3)+(9*q)*(2*q^3)+(2*q^3)*(80*q^3) := by
        simp only [abs_mul,abs_neg,abs_of_pos hq0,abs_of_nonneg (show (0:ℝ) ≤ 9 by norm_num)]
        gcongr
      _ = _ := by ring
  have hp (n : ℕ) : q^(n+1) ≤ q*(1/4)^n := by
    rw [pow_succ]
    calc
      q^n*q ≤ (1/4:ℝ)^n*q := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0.le hq n) hq0.le
      _ = _ := by ring
  have hp3 := hp 2
  have hp4 := hp 3
  have hp6 := hp 5
  norm_num at hp3 hp4 hp6
  have hl := (abs_le.mp herr).1
  linarith

 theorem halfThetaSum_determinant_pos {q : ℝ} (hq0 : 0 < q) (hq : q ≤ 1/4) :
    0 < halfThetaSum halfWeightB q*halfThetaSum halfWeightE q-
      halfThetaSum halfWeightA q*halfThetaSum halfWeightJ q := by
  obtain ⟨hA,hB,hE,hJ⟩ := halfTheta_remainder_bounds hq0.le hq
  exact halfThetaDeterminant_pos hq0 hq hA hB hE hJ

 theorem halfThetaSum_A_pos {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1/4) :
    0 < halfThetaSum halfWeightA q := by
  have ha := (abs_le.mp (halfTheta_remainder_bounds hq0 hq).1).1
  have hq3 : q^3 ≤ (1/4:ℝ)^3 := pow_le_pow_left₀ hq0 hq 3
  norm_num at hq3
  linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.halfThetaSum_determinant_pos
