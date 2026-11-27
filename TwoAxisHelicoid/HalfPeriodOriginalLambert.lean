import TwoAxisHelicoid.HalfPeriodPositiveSeries
import TwoAxisHelicoid.EtaLambertExpansion

namespace TwoAxisHelicoid
open ArithmeticFunction

/-- The first (signed Lambert) series in the displayed Fourier formula
for F in Section 5, with the same nome, coefficients and denominators as
the manuscript. It is absolutely convergent and agrees with the actual
half-period value for every positive parameter. -/
theorem ellipticFReal_manuscript_signed_lambert {t : ℝ} (ht : 0<t) :
    let q := Real.exp (-Real.pi*t)
    let term := fun n : ℕ => (n+1:ℝ)*((-1:ℝ)^(n+1)*q^(n+1)-3*q^(2*(n+1)))/(1-q^(2*(n+1)))
    Summable term ∧ ellipticFReal t=Real.pi^2/4+2*Real.pi^2*∑' n, term n := by
  let q := Real.exp (-Real.pi*t)
  let L := fun (r : ℝ) (n : ℕ) => (n+1:ℝ)*r^(n+1)/(1-r^(n+1))
  let T := fun n : ℕ => (n+1:ℝ)*((-1:ℝ)^(n+1)*q^(n+1)-3*q^(2*(n+1)))/(1-q^(2*(n+1)))
  have hq : |q|<1 := by
    rw [abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) ht
  have hn : |-q|<1 := by simpa only [abs_neg] using hq
  have hq2 : |q^2|<1 := by rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg q) hq (by decide)
  have S (r : ℝ) (hr : |r|<1) : Summable (L r) := by
    have h := summable_norm_pow_mul_geometric_div_one_sub 1 (show ‖r‖<1 from hr)
    simpa only [L,pow_one,Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr h
  have lambert (r : ℝ) (hr : |r|<1) :
      (∑' n : ℕ, (sigma 1 (n+1):ℝ)*r^(n+1))=∑' n, L r n := by
    rw [← jacobiFraction_series_eq_sigma (show ‖r‖<1 from hr)]
    exact (lambert_linear_eq_jacobi_fraction hr).symm
  have term (n : ℕ) : L (-q) n-4*L (q^2) n=T n := by
    let x := (-q)^(n+1)
    have ax : |x|<1 := by dsimp [x];rw [abs_pow];exact pow_lt_one₀ (abs_nonneg _) hn (Nat.succ_ne_zero n)
    have hx := abs_lt.mp ax
    have denom : 1-x^2≠0 := by nlinarith [mul_pos (sub_pos.mpr hx.2) (by linarith : 0<1+x)]
    have base : (q^2)^(n+1)=x^2 := by
      calc (q^2)^(n+1)=((-q)^2)^(n+1) := by rw [neg_sq]
           _=(-q)^(2*(n+1)) := (pow_mul _ _ _).symm
           _=(-q)^((n+1)*2) := by rw [Nat.mul_comm 2 (n+1)]
           _=x^2 := pow_mul _ _ _
    have d : q^(2*(n+1))=x^2 := by rw [pow_mul,base]
    have sign : (-1:ℝ)^(n+1)*q^(n+1)=x := by rw [← mul_pow];simp [x]
    change (n+1:ℝ)*x/(1-x)-4*((n+1:ℝ)*(q^2)^(n+1)/(1-(q^2)^(n+1)))=T n
    dsimp only [T]
    rw [base,d,sign]
    field_simp [denom,sub_ne_zero.mpr (ne_of_gt hx.2)]
    ring
  change Summable T ∧ ellipticFReal t=Real.pi^2/4+2*Real.pi^2*∑' n, T n
  have merged := (S (-q) hn).sub ((S (q^2) hq2).mul_left 4)
  refine ⟨merged.congr term,?_⟩
  have hf := ellipticFReal_sigma_series ht
  change ellipticFReal t=Real.pi^2*(1/4+2*(∑' n : ℕ, (sigma 1 (n+1):ℝ)*(-q)^(n+1))-
    8*(∑' n : ℕ, (sigma 1 (n+1):ℝ)*((-q)^2)^(n+1))) at hf
  rw [neg_sq,lambert _ hn,lambert _ hq2] at hf
  rw [← tsum_congr term,(S (-q) hn).tsum_sub ((S (q^2) hq2).mul_left 4),tsum_mul_left,hf]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.ellipticFReal_manuscript_signed_lambert
