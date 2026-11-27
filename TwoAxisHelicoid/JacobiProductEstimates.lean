import TwoAxisHelicoid.JacobiProductBasic

namespace TwoAxisHelicoid
open Complex Filter Set
open scoped Topology
set_option maxHeartbeats 0

theorem jacobi_factor_norm_tsum {q : ℂ} (hq : ‖q‖ < 1) (x : ℂ) :
    (∑' n : ℕ, ‖q^(n+1)*x‖) = ‖q‖*‖x‖/(1-‖q‖) := by
  simp only [norm_mul, norm_pow, pow_succ, mul_assoc]
  rw [tsum_mul_right, tsum_geometric_of_norm_lt_one (by simpa using hq)]
  ring

/-- A bound for the actual infinite product, obtained by taking limits of
the finite product estimate; no truncation is used as an assumption. -/
theorem jacobiFactorProduct_sub_one_norm_le {q : ℂ} (hq : ‖q‖ < 1) (x : ℂ) :
    ‖jacobiFactorProduct q x-1‖ ≤ Real.exp (‖q‖*‖x‖/(1-‖q‖))-1 := by
  let f : ℕ → ℂ := fun n => -(q^(n+1)*x)
  have hs : Summable (fun n => ‖f n‖) := by
    simpa only [f, norm_neg] using jacobi_factor_norm_summable hq x
  have hp : HasProd (fun n : ℕ => 1-q^(n+1)*x) (jacobiFactorProduct q x) :=
    (jacobiFactorProduct_multipliable hq x).hasProd
  have ht := (hp.sub_const (1 : ℂ)).norm
  have hb : ‖jacobiFactorProduct q x-1‖ ≤ Real.exp (∑' n, ‖f n‖)-1 := by
    apply le_of_tendsto ht
    apply Eventually.of_forall
    intro s
    simpa only [f, sub_eq_add_neg] using (Finset.norm_prod_one_add_sub_one_le s f).trans
      (sub_le_sub_right (Real.exp_le_exp.mpr (hs.sum_le_tsum s (fun n _ => norm_nonneg (f n)))) 1)
  simpa only [f, norm_neg, jacobi_factor_norm_tsum hq x] using hb

theorem jacobiPairProduct_sub_one_norm_le {q : ℂ} (hq : ‖q‖ < 1) (x : ℂ) :
    ‖jacobiPairProduct q x-1‖ ≤
      Real.exp (‖q‖*‖x‖/(1-‖q‖)+‖q‖*‖x⁻¹‖/(1-‖q‖))-1 := by
  let u := jacobiFactorProduct q x
  let v := jacobiFactorProduct q x⁻¹
  let A := ‖q‖*‖x‖/(1-‖q‖)
  let B := ‖q‖*‖x⁻¹‖/(1-‖q‖)
  have ha : ‖u-1‖ ≤ Real.exp A-1 := jacobiFactorProduct_sub_one_norm_le hq x
  have hb : ‖v-1‖ ≤ Real.exp B-1 := jacobiFactorProduct_sub_one_norm_le hq x⁻¹
  have hA : 0 ≤ Real.exp A-1 := (norm_nonneg (u-1)).trans ha
  have hv : ‖v‖ ≤ Real.exp B := by
    have hv' := norm_le_norm_sub_add v (1 : ℂ)
    norm_num only [norm_one] at hv'
    linarith
  have hm := mul_le_mul ha hv (norm_nonneg v) hA
  change ‖u*v-1‖ ≤ Real.exp (A+B)-1
  calc
    ‖u*v-1‖ = ‖(u-1)*v+(v-1)‖ := by congr 1; ring
    _ ≤ ‖u-1‖*‖v‖+‖v-1‖ := by simpa only [norm_mul] using norm_add_le ((u-1)*v) (v-1)
    _ ≤ (Real.exp A-1)*Real.exp B+(Real.exp B-1) := add_le_add hm hb
    _ = Real.exp (A+B)-1 := by rw [Real.exp_add]; ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiFactorProduct_sub_one_norm_le
#print axioms TwoAxisHelicoid.jacobiPairProduct_sub_one_norm_le
