import TwoAxisHelicoid.HalfThetaWeights

namespace TwoAxisHelicoid

theorem thetaTriangular_six_lower (n : ℕ) : 21+7*n ≤ thetaTriangular (n+6) := by
  induction n with
  | zero => norm_num [thetaTriangular]
  | succ n ih => simp only [thetaTriangular]; omega

theorem oddSquare_six_upper (n : ℕ) : (2*((n+6:ℕ):ℝ)+1)^2 ≤ 169*2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have he : (2*((n+1+6:ℕ):ℝ)+1)^2 ≤ 2*(2*((n+6:ℕ):ℝ)+1)^2 := by
      push_cast
      nlinarith [sq_nonneg (n:ℝ),Nat.cast_nonneg (α := ℝ) n]
    rw [pow_succ 2 n]
    linarith

theorem halfThetaB_six_term_bound {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1/4) (n : ℕ) :
    |halfThetaTerm halfWeightB q (n+6)| ≤ (169*q^21)*(1/8192)^n := by
  have hq1 : q ≤ 1 := by linarith
  have hq7 : q^7 ≤ (1/16384:ℝ) := by
    convert pow_le_pow_left₀ hq0 hq 7 using 1
    norm_num
  have hpow : q^(thetaTriangular (n+6)) ≤ q^(21+7*n) :=
    pow_le_pow_of_le_one hq0 hq1 (thetaTriangular_six_lower n)
  calc
    |halfThetaTerm halfWeightB q (n+6)| = (2*((n+6:ℕ):ℝ)+1)^2*q^(thetaTriangular (n+6)) := by
      simp only [halfThetaTerm,halfWeightB,abs_mul,halfThetaSign_abs,one_mul,
        abs_of_nonneg (sq_nonneg (2*((n+6:ℕ):ℝ)+1)),abs_of_nonneg (pow_nonneg hq0 _)]
    _ ≤ (169*2^n)*q^(21+7*n) :=
      mul_le_mul (oddSquare_six_upper n) hpow (pow_nonneg hq0 _) (by positivity)
    _ = (169*q^21)*(2*q^7)^n := by rw [pow_add,pow_mul,mul_pow]; ring
    _ ≤ (169*q^21)*(1/8192)^n := by gcongr; nlinarith

theorem halfThetaB_six_error {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1/4) :
    |halfThetaSum halfWeightB q-(1-9*q-25*q^3+49*q^6+81*q^10-121*q^15)| ≤ 1/10^10 := by
  have hB := (halfThetaB_tail hq0 hq).1
  have hs : Summable (fun n => halfThetaTerm halfWeightB q (n+6)) := (summable_nat_add_iff 6).mpr hB
  have hf : (∑ n ∈ Finset.range 6, halfThetaTerm halfWeightB q n) =
      1-9*q-25*q^3+49*q^6+81*q^10-121*q^15 := by
    norm_num [Finset.sum_range_succ,halfThetaTerm,halfWeightB,halfThetaSign,thetaSign,thetaTriangular]
    ring
  have he : halfThetaSum halfWeightB q-(1-9*q-25*q^3+49*q^6+81*q^10-121*q^15) =
      ∑' n, halfThetaTerm halfWeightB q (n+6) := by
    unfold halfThetaSum
    rw [← hB.sum_add_tsum_nat_add 6,hf]
    ring
  have hgeo : Summable (fun n : ℕ => (169*q^21)*(1/8192:ℝ)^n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/8192:ℝ)‖ < 1)).mul_left _
  rw [he]
  calc
    |∑' n, halfThetaTerm halfWeightB q (n+6)| ≤ ∑' n, |halfThetaTerm halfWeightB q (n+6)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : ℕ, (169*q^21)*(1/8192:ℝ)^n :=
      hs.abs.tsum_le_tsum (halfThetaB_six_term_bound hq0 hq) hgeo
    _ = (169*q^21)/(1-1/8192) := by
      rw [tsum_mul_left,tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/8192:ℝ)‖ < 1)]
      ring
    _ ≤ (169*(1/4:ℝ)^21)/(1-1/8192) := by gcongr
    _ ≤ 1/10^10 := by norm_num

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.halfThetaB_six_error
