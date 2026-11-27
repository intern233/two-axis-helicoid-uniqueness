import TwoAxisHelicoid.HalfThetaSeries

namespace TwoAxisHelicoid

noncomputable def halfWeightA (_ : ℕ) : ℝ := 1
noncomputable def halfWeightB (n : ℕ) : ℝ := (2*n+1)^2
noncomputable def halfWeightE (n : ℕ) : ℝ := thetaTriangular n
noncomputable def halfWeightJ (n : ℕ) : ℝ := (2*n+1)^2*thetaTriangular n
noncomputable def halfThetaSum (w : ℕ → ℝ) (q : ℝ) : ℝ := ∑' n, halfThetaTerm w q n

 theorem halfWeightB_eq (n : ℕ) : halfWeightB n = 8*halfWeightE n+1 := by
  simp only [halfWeightB,halfWeightE,thetaTriangular_real]
  ring

theorem halfThetaSum_split {w : ℕ → ℝ} {q : ℝ} (hs : Summable (halfThetaTerm w q)) :
    halfThetaSum w q = w 0-w 1*q+halfThetaTail w q := by
  unfold halfThetaSum halfThetaTail
  rw [← hs.sum_add_tsum_nat_add 2]
  simp [Finset.sum_range_succ,halfThetaTerm,halfThetaSign_zero,halfThetaSign_one,thetaTriangular]
  ring

theorem halfThetaA_tail {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1/4) :
    Summable (halfThetaTerm halfWeightA q) ∧ |halfThetaTail halfWeightA q| ≤ 2*q^3 := by
  have h := halfThetaTail_bound (w := halfWeightA) (C := 1) (b := 1) hq0 hq
    (by norm_num) (by norm_num) (by norm_num) (by intro n; simp [halfWeightA])
  refine ⟨(summable_nat_add_iff 2).mp h.1,h.2.trans ?_⟩
  nlinarith [pow_nonneg hq0 3]

theorem halfThetaB_tail {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1/4) :
    Summable (halfThetaTerm halfWeightB q) ∧ |halfThetaTail halfWeightB q| ≤ 26*q^3 := by
  have h := halfThetaTail_bound (w := halfWeightB) (C := 25) (b := 2) hq0 hq
    (by norm_num) (by norm_num) (by norm_num) (by
      intro n
      rw [halfWeightB,abs_of_nonneg (sq_nonneg _)]
      exact oddSquare_tail_upper n)
  refine ⟨(summable_nat_add_iff 2).mp h.1,h.2.trans ?_⟩
  nlinarith [pow_nonneg hq0 3]

theorem halfThetaE_tail {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1/4) :
    Summable (halfThetaTerm halfWeightE q) ∧ |halfThetaTail halfWeightE q| ≤ 4*q^3 := by
  have h := halfThetaTail_bound (w := halfWeightE) (C := 3) (b := 2) hq0 hq
    (by norm_num) (by norm_num) (by norm_num) (by
      intro n
      rw [halfWeightE,abs_of_nonneg (Nat.cast_nonneg _)]
      exact thetaTriangular_tail_upper n)
  refine ⟨(summable_nat_add_iff 2).mp h.1,h.2.trans ?_⟩
  nlinarith [pow_nonneg hq0 3]

theorem halfThetaJ_tail {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1/4) :
    Summable (halfThetaTerm halfWeightJ q) ∧ |halfThetaTail halfWeightJ q| ≤ 80*q^3 := by
  have h := halfThetaTail_bound (w := halfWeightJ) (C := 75) (b := 4) hq0 hq
    (by norm_num) (by norm_num) (by norm_num) (by
      intro n
      rw [halfWeightJ,abs_of_nonneg (by positivity)]
      calc
        (2*((n+2:ℕ):ℝ)+1)^2*(thetaTriangular (n+2):ℝ) ≤ (25*2^n)*(3*2^n) :=
          mul_le_mul (oddSquare_tail_upper n) (thetaTriangular_tail_upper n)
            (Nat.cast_nonneg _) (by positivity)
        _ = 75*4^n := by rw [show (4:ℝ)=2*2 by norm_num,mul_pow]; ring)
  refine ⟨(summable_nat_add_iff 2).mp h.1,?_⟩
  convert h.2 using 1
  norm_num

theorem halfTheta_remainder_bounds {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1/4) :
    |halfThetaSum halfWeightA q-(1-q)| ≤ 2*q^3 ∧
    |halfThetaSum halfWeightB q-(1-9*q)| ≤ 26*q^3 ∧
    |halfThetaSum halfWeightE q-(-q)| ≤ 4*q^3 ∧
    |halfThetaSum halfWeightJ q-(-9*q)| ≤ 80*q^3 := by
  have hA := halfThetaA_tail hq0 hq
  have hB := halfThetaB_tail hq0 hq
  have hE := halfThetaE_tail hq0 hq
  have hJ := halfThetaJ_tail hq0 hq
  rw [halfThetaSum_split hA.1,halfThetaSum_split hB.1,halfThetaSum_split hE.1,halfThetaSum_split hJ.1]
  norm_num [halfWeightA,halfWeightB,halfWeightE,halfWeightJ,thetaTriangular]
  simpa only [add_sub_cancel_left] using And.intro hA.2 (And.intro hB.2 (And.intro hE.2 hJ.2))

end TwoAxisHelicoid
