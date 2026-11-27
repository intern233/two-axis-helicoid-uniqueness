import TwoAxisHelicoid.ThetaPhase
import TwoAxisHelicoid.ThetaConvergence
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace TwoAxisHelicoid
open Complex

noncomputable def thetaBilateralTerm (t : ℝ) (n : ℤ) (v : ℂ) : ℂ :=
  thetaPhase n * exp (-Real.pi*t*n*(n+1)/2+(2*n+1)*v*I)

noncomputable def thetaComplexHalfPeriod (t : ℝ) : ℂ := Real.pi*(1+I*t)/2
noncomputable def thetaQuasiFactor (t : ℝ) (v : ℂ) : ℂ :=
  exp (Real.pi*I/2+Real.pi*t/2-2*v*I)

theorem thetaBilateralTerm_shift (t : ℝ) (n : ℤ) (v : ℂ) :
    thetaBilateralTerm t n (v+thetaComplexHalfPeriod t) =
      thetaQuasiFactor t v*thetaBilateralTerm t (n+1) v := by
  unfold thetaBilateralTerm thetaPhase thetaQuasiFactor thetaComplexHalfPeriod
  simp only [Int.cast_add, Int.cast_one, ← Complex.exp_add]
  congr 1
  ring_nf
  simp only [I_sq]; ring

theorem thetaBilateralTerm_negative (t : ℝ) (n : ℤ) (v : ℂ) :
    thetaBilateralTerm t (-n-1) v = -thetaBilateralTerm t n (-v) := by
  unfold thetaBilateralTerm
  simp only [Int.cast_sub, Int.cast_neg, Int.cast_one, thetaPhase_int_neg_sub_one]
  have he : (-Real.pi*t*(-n-1)*((-n-1)+1)/2+(2*(-n-1)+1)*v*I : ℂ) =
      -Real.pi*t*n*(n+1)/2+(2*n+1)*(-v)*I := by ring
  rw [he]
  ring

theorem thetaBilateralTerm_nat (t : ℝ) (n : ℕ) (v : ℂ) :
    thetaBilateralTerm t n v = thetaSign n *
      (Real.exp (-Real.pi*t*n*(n+1)/2) : ℂ) * exp ((2*n+1 : ℂ)*v*I) := by
  unfold thetaBilateralTerm
  simp only [Int.cast_natCast, thetaPhase_nat, Complex.exp_add, Complex.ofReal_exp]
  push_cast
  ring

theorem thetaBilateralTerm_pair (t : ℝ) (n : ℕ) (v : ℂ) :
    thetaBilateralTerm t n v+thetaBilateralTerm t (-((n : ℤ)+1)) v =
      (2*I)*thetaTerm t 0 n v := by
  rw [show -((n : ℤ)+1) = -(n : ℤ)-1 by ring, thetaBilateralTerm_negative,
    thetaBilateralTerm_nat, thetaBilateralTerm_nat]
  simp only [thetaTerm, sineJet, pow_zero, one_mul]
  have he : (2*n+1 : ℂ)*(-v)*I = -((2*n+1 : ℂ)*v)*I := by ring
  rw [he]
  field_simp
  ring

theorem thetaBilateralTerm_nat_norm_le (t : ℝ) (n : ℕ) (v : ℂ) :
    ‖thetaBilateralTerm t n v‖ ≤ thetaMajorant t |v.im| 0 n := by
  rw [thetaBilateralTerm_nat, norm_mul, norm_mul, thetaSign_norm, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.norm_exp,
    ← Real.exp_add]
  unfold thetaMajorant
  simp only [pow_zero, one_mul]
  apply Real.exp_le_exp.mpr
  have he : (((2*n+1 : ℂ)*v*I).re) = -(2*(n : ℝ)+1)*v.im := by
    norm_num [Complex.mul_re, Complex.mul_im]; ring
  rw [he]
  have h := mul_le_mul_of_nonneg_left (neg_le_abs v.im) (show (0 : ℝ) ≤ 2*n+1 by positivity)
  linarith

theorem thetaBilateralTerm_nat_summable {t : ℝ} (ht : 0 < t) (v : ℂ) :
    Summable (fun n : ℕ => thetaBilateralTerm t n v) :=
  Summable.of_norm_bounded (thetaMajorant_summable ht |v.im| 0)
    (fun n => thetaBilateralTerm_nat_norm_le t n v)

attribute [local irreducible] thetaBilateralTerm thetaPhase thetaTerm

theorem thetaBilateralTerm_summable {t : ℝ} (ht : 0 < t) (v : ℂ) :
    Summable (fun n : ℤ => thetaBilateralTerm t n v) := by
  apply Summable.of_nat_of_neg_add_one (thetaBilateralTerm_nat_summable ht v)
  have h := (thetaBilateralTerm_nat_summable ht (-v)).neg
  convert h using 1
  funext n
  rw [show -((n : ℤ)+1) = -(n : ℤ)-1 by ring, thetaBilateralTerm_negative]

theorem thetaBilateral_sum {t : ℝ} (ht : 0 < t) (v : ℂ) :
    (∑' n : ℤ, thetaBilateralTerm t n v) = (2*I)*thetaJet t 0 v := by
  rw [← tsum_nat_add_neg_add_one (thetaBilateralTerm_summable ht v)]
  simp only [thetaBilateralTerm_pair, tsum_mul_left, thetaJet]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaBilateral_sum
