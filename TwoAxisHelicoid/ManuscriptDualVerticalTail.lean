import TwoAxisHelicoid.ManuscriptDualVerticalSeries
import TwoAxisHelicoid.LambertTail

namespace TwoAxisHelicoid

noncomputable def manuscriptWeightedTail (x : ℝ) (N : ℕ) : ℝ :=
  x^N*(((N:ℝ)+1)/(1-x)+x/(1-x)^2)

/-- The series for T_N includes x=0 and N=0. -/
theorem manuscript_weighted_tail_hasSum {x : ℝ} (hx : 0≤x) (h1 : x<1) (N : ℕ) :
    HasSum (fun j : ℕ => ((j+N+1:ℕ):ℝ)*x^(j+N)) (manuscriptWeightedTail x N) := by
  have h : ‖x‖<1 := by simpa only [Real.norm_eq_abs,abs_of_nonneg hx] using h1
  have a := (hasSum_geometric_of_norm_lt_one h).mul_left ((N:ℝ)+1)
  have b := hasSum_coe_mul_geometric_of_norm_lt_one h
  convert (a.add b).mul_left (x^N) using 1
  · ext j
    simp only [Nat.cast_add,Nat.cast_one,pow_add]
    ring
  · unfold manuscriptWeightedTail
    ring

private theorem dual_vertical_term_majorant {q E : ℝ} (hq : 0<q) (h1 : q<1) (hE : 0<E) (j : ℕ) :
    |dualVerticalLambertTerm q E j|≤
      ((j+1:ℕ):ℝ)*(E*(q*E)^j+(q^2/E)*(q^3/E)^j)/(1-q^2) := by
  have hq2 : q^2<1 := by nlinarith [mul_pos (sub_pos.mpr h1) (by linarith : 0<1+q)]
  have bound : (-q^2)^(j+1)≤q^2 := by
    calc _ ≤ |(-q^2)^(j+1)| := le_abs_self _
         _ = (q^2)^(j+1) := by rw [abs_pow,abs_neg,abs_sq]
         _ ≤ q^2 := pow_le_of_le_one (sq_nonneg q) hq2.le (Nat.succ_ne_zero j)
  have den : 1-q^2≤1-(-q^2)^(j+1) := by linarith
  have dp := (sub_pos.mpr hq2).trans_le den
  have alg : q^j*(E^(j+1)+q^(2*(j+1))*(E⁻¹)^(j+1))=
      E*(q*E)^j+(q^2/E)*(q^3/E)^j := by
    simp only [div_eq_mul_inv,mul_pow,pow_mul,pow_succ]
    simp only [pow_zero,one_mul]
    ring
  have sign : |(-1:ℝ)^(j+2)|=1 := by rw [abs_pow];norm_num
  rw [dualVerticalLambertTerm,abs_div,abs_of_pos dp,abs_mul,abs_mul,abs_mul,sign,one_mul,
    abs_of_nonneg (Nat.cast_nonneg _),abs_of_pos (pow_pos hq _),abs_of_pos (by positivity : 0<E^(j+1)+q^(2*(j+1))*(E⁻¹)^(j+1)),
    mul_assoc,alg]
  exact div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hq2) den

/-- For each truncation index the omitted part of the actual signed
series is bounded by the expression in equation two_axis_helicoid:eq-D-tail. -/
theorem manuscript_dual_vertical_tail_bound {q E : ℝ} (hq : 0<q) (h1 : q<1) (hE : 0<E)
    (up : q*E<1) (down : q^3/E<1) (N : ℕ) :
    |(∑' j : ℕ, dualVerticalLambertTerm q E j)-
      ∑ j ∈ Finset.range N, dualVerticalLambertTerm q E j|≤
      (E*manuscriptWeightedTail (q*E) N+(q^2/E)*manuscriptWeightedTail (q^3/E) N)/(1-q^2) := by
  have a := (manuscript_weighted_tail_hasSum (mul_pos hq hE).le up N).mul_left E
  have b := (manuscript_weighted_tail_hasSum (by positivity : 0≤q^3/E) down N).mul_left (q^2/E)
  let major := fun j : ℕ => ((j+N+1:ℕ):ℝ)*(E*(q*E)^(j+N)+(q^2/E)*(q^3/E)^(j+N))/(1-q^2)
  have hm : HasSum major ((E*manuscriptWeightedTail (q*E) N+
      (q^2/E)*manuscriptWeightedTail (q^3/E) N)/(1-q^2)) := by
    apply ((a.add b).div_const (1-q^2)).congr_fun
    intro j
    dsimp only [major]
    ring
  have hb (j : ℕ) : ‖dualVerticalLambertTerm q E (j+N)‖≤major j :=
    dual_vertical_term_majorant hq h1 hE (j+N)
  have norms := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hm.summable
  have sum := (jacobiRealE_eq_manuscript_D hq h1 hE up down).1.sum_add_tsum_nat_add N
  rw [← sum,add_sub_cancel_left]
  exact (norm_tsum_le_tsum_norm norms).trans ((norms.tsum_le_tsum hb hm.summable).trans_eq hm.tsum_eq)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.manuscript_weighted_tail_hasSum
#print axioms TwoAxisHelicoid.manuscript_dual_vertical_tail_bound

