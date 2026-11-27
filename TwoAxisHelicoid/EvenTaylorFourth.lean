import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Filter
open scoped Topology

theorem even_analytic_fourth_decomposition {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0)
    (he : (fun x : ℝ => f (-x)) =ᶠ[𝓝 0] f) :
    ∃ c : ℝ, ∃ R : ℝ → ℝ, AnalyticAt ℝ R 0 ∧
      ∀ᶠ x in 𝓝 0, f x = f 0+c*x^2+x^4*R x := by
  have hodd (n : ℕ) (hn : Odd n) : iteratedDeriv n f 0 = 0 := by
    have h := he.iteratedDeriv_eq n
    rw [iteratedDeriv_comp_neg] at h
    simp only [neg_zero,hn.neg_one_pow,neg_one_smul] at h
    linarith
  obtain ⟨R,hR,hrem⟩ := hf.exists_eventuallyEq_sum_add_pow_mul 4
  refine ⟨iteratedDeriv 2 f 0/2,R,hR,?_⟩
  filter_upwards [hrem] with x hx
  have h1 := hodd 1 (by decide)
  have h3 := hodd 3 (by decide)
  norm_num [Finset.sum_range_succ,h1,h3,smul_eq_mul] at hx
  linear_combination hx

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.even_analytic_fourth_decomposition
