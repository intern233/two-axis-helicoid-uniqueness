import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace TwoAxisHelicoid
open Complex

/-- A uniform contraction of image area between concentric dyadic
disks, together with the local diameter bound, gives an integral
power modulus of continuity at their common center. -/
theorem dyadic_disk_power_modulus (A : ℝ → ℝ) (g : ℂ → ℂ) {R q B : ℝ}
    (hR : 0<R) (hq : 0≤q) (hq1 : q<1) (hB : 0≤B)
    (area : 0≤A R) (shrink : ∀ r, 0<r → r≤R → A (r/2)≤q*A r)
    (diam : ∀ r, 0<r → r≤R → ∀ z : ℂ, ‖z‖≤r/2 → ‖g z‖^2≤B*A r) :
    ∃ N : ℕ, 0<N ∧ ∃ C : ℝ, 0<C ∧
      ∀ z : ℂ, 0<‖z‖ → ‖z‖≤R/2 → ‖g z‖^N≤C*‖z‖ := by
  let d : ℝ := 1/2
  have hd : 0<d := by norm_num [d]
  have hd1 : d<1 := by norm_num [d]
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one hd hq1
  have kp : 0<k := by
    by_contra! h
    have eq : k=0 := by omega
    rw [eq,pow_zero] at hk
    exact hd1.not_gt hk
  have pos (n : ℕ) : 0<R*d^n := mul_pos hR (pow_pos hd n)
  have small (n : ℕ) : R*d^n≤R := (mul_le_mul_of_nonneg_left (pow_le_one₀ hd.le hd1.le) hR.le).trans_eq (mul_one R)
  have ad (n : ℕ) : A (R*d^n)≤q^n*A R := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show R*d^(n+1)=R*d^n/2 by rw [pow_succ]; dsimp [d]; ring]
      exact (shrink _ (pos _) (small _)).trans ((mul_le_mul_of_nonneg_left ih hq).trans_eq (by rw [pow_succ]; ring))
  let D := (B*A R)^k
  have dpos : 0≤D := pow_nonneg (mul_nonneg hB area) _
  refine ⟨2*k,by omega,4*(D+1)/R,by positivity,?_⟩
  intro z nz near
  have x0 : 0<2*‖z‖/R := by positivity
  have x1 : 2*‖z‖/R≤1 := by rw [div_le_iff₀ hR]; linarith
  obtain ⟨n,lb,ub⟩ := exists_nat_pow_near_of_lt_one x0 x1 hd hd1
  have zn : ‖z‖≤(R*d^n)/2 := by
    have b := (div_le_iff₀ hR).mp ub
    linarith [mul_comm (d^n) R]
  have dm := (diam _ (pos n) (small n) z zn).trans (mul_le_mul_of_nonneg_left (ad n) hB)
  have powered := pow_le_pow_left₀ (sq_nonneg _) dm k
  have cp : (q^n)^k≤d^n := by
    rw [← pow_mul,Nat.mul_comm,pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg hq _) hk.le _
  have dn : d^n≤4*‖z‖/R := by
    rw [pow_succ] at lb
    dsimp [d] at lb ⊢
    have p := (lt_div_iff₀ hR).mp lb
    apply (le_div_iff₀ hR).mpr
    linarith
  calc
    ‖g z‖^(2*k) = (‖g z‖^2)^k := pow_mul _ _ _
    _ ≤ (B*(q^n*A R))^k := powered
    _ = (q^n)^k*D := by dsimp [D]; rw [show B*(q^n*A R)=q^n*(B*A R) by ring,mul_pow]
    _ ≤ d^n*D := mul_le_mul_of_nonneg_right cp dpos
    _ ≤ (4*‖z‖/R)*D := mul_le_mul_of_nonneg_right dn dpos
    _ ≤ (4*(D+1)/R)*‖z‖ := by
      have extra : 0≤4*‖z‖/R := by positivity
      calc
        _ ≤ (4*‖z‖/R)*D+4*‖z‖/R := le_add_of_nonneg_right extra
        _ = _ := by ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.dyadic_disk_power_modulus
