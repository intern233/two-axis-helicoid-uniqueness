import TwoAxisHelicoid.ThetaSymmetry
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace TwoAxisHelicoid
open Complex

/-- Integer triangular exponent in the normalized theta series. -/
def thetaTriangular : ℕ → ℕ
  | 0 => 0
  | n+1 => thetaTriangular n+n+1

theorem thetaTriangular_real (n : ℕ) : (thetaTriangular n:ℝ) = (n:ℝ)*(n+1)/2 := by
  induction n with
  | zero => norm_num [thetaTriangular]
  | succ n ih => simp only [thetaTriangular,Nat.cast_add,Nat.cast_one,ih]; ring

theorem thetaTriangular_tail_lower (n : ℕ) : 3+3*n ≤ thetaTriangular (n+2) := by
  induction n with
  | zero => norm_num [thetaTriangular]
  | succ n ih => simp only [thetaTriangular]; omega

theorem thetaTriangular_tail_upper (n : ℕ) : (thetaTriangular (n+2):ℝ) ≤ 3*2^n := by
  induction n with
  | zero => norm_num [thetaTriangular]
  | succ n ih =>
    have he : (thetaTriangular (n+1+2):ℝ) ≤ 2*(thetaTriangular (n+2):ℝ) := by
      norm_num only [thetaTriangular_real,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
      nlinarith [sq_nonneg (n:ℝ),Nat.cast_nonneg (α := ℝ) n]
    rw [pow_succ 2 n]
    linarith

theorem oddSquare_tail_upper (n : ℕ) : (2*(n+2:ℕ)+1:ℝ)^2 ≤ 25*2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have he : (2*((n+1:ℕ)+2)+1:ℝ)^2 ≤ 2*(2*(n+2:ℕ)+1:ℝ)^2 := by
      push_cast
      nlinarith [sq_nonneg (n:ℝ),Nat.cast_nonneg (α := ℝ) n]
    rw [pow_succ 2 n]
    norm_num only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at ih he ⊢
    linarith

noncomputable def halfThetaSign (n : ℕ) : ℝ := (thetaSign n).re*(-1)^n

theorem halfThetaSign_abs (n : ℕ) : |halfThetaSign n| = 1 := by
  unfold halfThetaSign thetaSign
  split_ifs <;> simp

theorem halfThetaSign_zero : halfThetaSign 0 = 1 := by norm_num [halfThetaSign,thetaSign]
theorem halfThetaSign_one : halfThetaSign 1 = -1 := by norm_num [halfThetaSign,thetaSign]

noncomputable def halfThetaTerm (w : ℕ → ℝ) (q : ℝ) (n : ℕ) : ℝ :=
  halfThetaSign n*w n*q^(thetaTriangular n)

noncomputable def halfThetaTail (w : ℕ → ℝ) (q : ℝ) : ℝ := ∑' n, halfThetaTerm w q (n+2)

/-- A geometric majorant that retains the factor q^3 of every omitted term. -/
theorem halfThetaTerm_tail_bound {w : ℕ → ℝ} {q C b : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1/4) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hw : ∀ n, |w (n+2)| ≤ C*b^n) (n : ℕ) :
    |halfThetaTerm w q (n+2)| ≤ (C*q^3)*(b/64)^n := by
  have hq1 : q ≤ 1 := by linarith
  have hq3 : q^3 ≤ (1/64:ℝ) := by nlinarith [sq_nonneg (q-1/4)]
  have hpow : q^(thetaTriangular (n+2)) ≤ q^(3+3*n) :=
    pow_le_pow_of_le_one hq0 hq1 (thetaTriangular_tail_lower n)
  calc
    |halfThetaTerm w q (n+2)| = |w (n+2)| * q^(thetaTriangular (n+2)) := by
      simp only [halfThetaTerm,abs_mul,halfThetaSign_abs,one_mul,abs_of_nonneg (pow_nonneg hq0 _)]
    _ ≤ (C*b^n)*q^(3+3*n) := mul_le_mul (hw n) hpow (pow_nonneg hq0 _) (by positivity)
    _ = (C*q^3)*(b*q^3)^n := by rw [pow_add,pow_mul,mul_pow]; ring
    _ ≤ (C*q^3)*(b/64)^n := by gcongr; nlinarith

theorem halfThetaTail_bound {w : ℕ → ℝ} {q C b : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1/4) (hC : 0 ≤ C) (hb : 0 ≤ b) (hb64 : b < 64)
    (hw : ∀ n, |w (n+2)| ≤ C*b^n) :
    Summable (fun n => halfThetaTerm w q (n+2)) ∧
      |halfThetaTail w q| ≤ (C/(1-b/64))*q^3 := by
  have hratio : ‖b/64‖ < 1 := by rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]; linarith
  have hsum : Summable (fun n : ℕ => (C*q^3)*(b/64)^n) :=
    (summable_geometric_of_norm_lt_one hratio).mul_left _
  have hs : Summable (fun n => halfThetaTerm w q (n+2)) :=
    Summable.of_norm_bounded hsum (fun n => by
      simpa only [Real.norm_eq_abs] using halfThetaTerm_tail_bound hq0 hq hC hb hw n)
  refine ⟨hs,?_⟩
  calc
    |halfThetaTail w q| ≤ ∑' n, |halfThetaTerm w q (n+2)| := by
      simpa only [Real.norm_eq_abs,halfThetaTail] using norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : ℕ, (C*q^3)*(b/64)^n :=
      hs.abs.tsum_le_tsum (halfThetaTerm_tail_bound hq0 hq hC hb hw) hsum
    _ = (C/(1-b/64))*q^3 := by rw [tsum_mul_left,tsum_geometric_of_norm_lt_one hratio]; ring

end TwoAxisHelicoid
