import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Complex Filter Set
open scoped Topology
set_option maxHeartbeats 0

/-- The one-sided product underlying the manuscript's Jacobi factors. -/
noncomputable def jacobiFactorProduct (q x : ℂ) : ℂ :=
  ∏' n : ℕ, (1-q^(n+1)*x)

noncomputable def jacobiPairProduct (q x : ℂ) : ℂ :=
  jacobiFactorProduct q x * jacobiFactorProduct q x⁻¹

theorem jacobi_factor_norm_summable {q : ℂ} (hq : ‖q‖ < 1) (x : ℂ) :
    Summable (fun n : ℕ => ‖q^(n+1)*x‖) := by
  have h := (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_right (‖q‖*‖x‖)
  simpa only [norm_mul, norm_pow, pow_succ, mul_assoc] using h

theorem jacobiFactorProduct_multipliable {q : ℂ} (hq : ‖q‖ < 1) (x : ℂ) :
    Multipliable (fun n : ℕ => 1-q^(n+1)*x) :=
  multipliable_one_sub_of_summable (jacobi_factor_norm_summable hq x)

theorem jacobiFactorProduct_ne_zero {q x : ℂ} (hq : ‖q‖ < 1)
    (hx : ∀ n : ℕ, 1-q^(n+1)*x ≠ 0) : jacobiFactorProduct q x ≠ 0 := by
  apply tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => -(q^(n+1)*x))
  · simpa only [sub_eq_add_neg] using hx
  · simpa only [norm_neg] using jacobi_factor_norm_summable hq x

theorem jacobiFactorProduct_ne_zero_of_norm {q x : ℂ} (hq : ‖q‖ < 1)
    (hx : ‖q‖*‖x‖ < 1) : jacobiFactorProduct q x ≠ 0 := by
  apply jacobiFactorProduct_ne_zero hq
  intro n hn
  have hp : ‖q‖^(n+1) ≤ ‖q‖ := by
    rw [pow_succ]
    have hb : ‖q‖^n ≤ 1 := pow_le_one₀ (norm_nonneg q) hq.le
    simpa using mul_le_mul_of_nonneg_right hb (norm_nonneg q)
  have hlt : ‖q^(n+1)*x‖ < 1 := by
    rw [norm_mul, norm_pow]
    exact (mul_le_mul_of_nonneg_right hp (norm_nonneg x)).trans_lt hx
  have he : q^(n+1)*x = 1 := (sub_eq_zero.mp hn).symm
  simp only [he, norm_one, lt_self_iff_false] at hlt

theorem jacobiFactorProduct_locally_uniform {q : ℂ} (hq : ‖q‖ < 1) :
    MultipliableLocallyUniformlyOn (fun n : ℕ => fun x : ℂ => 1-q^(n+1)*x) univ := by
  use jacobiFactorProduct q
  simp only [sub_eq_add_neg]
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  rcases K.eq_empty_or_nonempty with he | hne
  · simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn, he] using tendstoUniformlyOn_empty
  · obtain ⟨x₀, _, _, hbound⟩ := hK.exists_sSup_image_eq_and_ge hne
      (show ContinuousOn (fun x : ℂ => ‖x‖) K by fun_prop)
    have hs : Summable (fun n : ℕ => ‖q‖^(n+1)*‖x₀‖) := by
      simpa only [norm_mul, norm_pow] using jacobi_factor_norm_summable hq x₀
    apply hs.hasProdUniformlyOn_nat_one_add hK
      (.of_forall fun n x hx => ?_) (fun n => by fun_prop)
    simpa only [norm_neg, norm_mul, norm_pow] using
      mul_le_mul_of_nonneg_left (hbound x hx) (pow_nonneg (norm_nonneg q) (n+1))

theorem jacobiFactorProduct_differentiable {q : ℂ} (hq : ‖q‖ < 1) :
    Differentiable ℂ (jacobiFactorProduct q) := by
  apply differentiableOn_univ.mp
  exact (jacobiFactorProduct_locally_uniform hq).hasProdLocallyUniformlyOn.differentiableOn
    (.of_forall fun _ => by simpa [Finset.prod_fn] using
      DifferentiableOn.finsetProd (fun _ _ => by fun_prop)) isOpen_univ

theorem jacobiFactorProduct_shift {q : ℂ} (hq : ‖q‖ < 1) (x : ℂ) :
    (1-q*x)*jacobiFactorProduct q (q*x) = jacobiFactorProduct q x := by
  have hs : Multipliable (fun n : ℕ => 1-q^((n+1)+1)*x) := by
    simpa only [pow_succ, mul_assoc] using jacobiFactorProduct_multipliable hq (q*x)
  simpa [jacobiFactorProduct, pow_succ, mul_assoc] using
    (tprod_eq_zero_mul' (f := fun n : ℕ => 1-q^(n+1)*x) hs).symm

theorem jacobiFactorProduct_zero (q : ℂ) : jacobiFactorProduct q 0 = 1 := by
  simp [jacobiFactorProduct]

theorem jacobiPairProduct_differentiableOn {q : ℂ} (hq : ‖q‖ < 1) :
    DifferentiableOn ℂ (jacobiPairProduct q) {x : ℂ | x ≠ 0} := by
  intro x hx
  apply DifferentiableAt.differentiableWithinAt
  exact (jacobiFactorProduct_differentiable hq x).mul
    ((jacobiFactorProduct_differentiable hq x⁻¹).comp x (differentiableAt_inv hx))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiFactorProduct_differentiable
#print axioms TwoAxisHelicoid.jacobiFactorProduct_shift
