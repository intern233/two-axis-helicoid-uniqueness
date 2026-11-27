import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Complex

noncomputable def logSecondNumerator (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (c z : ℂ) : ℂ :=
  ((F 1 z)^2-F 2 z*F 0 z)*z^2-(F 0 z)^2-(g z+c)*(F 0 z)^2*z^2

attribute [local fun_prop] AnalyticAt.contDiffAt in
theorem logSecondNumerator_derivatives_vanish
    (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (c : ℂ)
    (hF : ∀ j, AnalyticAt ℂ (F j) 0) (hg : AnalyticAt ℂ g 0)
    (hD : ∀ j n, iteratedDeriv n (F j) 0 = F (j+n) 0)
    (h0 : F 0 0 = 0) (h2 : F 2 0 = 0) (hg0 : g 0 = 0)
    (hc : 3*c*F 1 0+F 3 0 = 0) {n : ℕ} (hn : n < 5) :
    iteratedDeriv n (logSecondNumerator F g c) 0 = 0 := by
  have hf0 := hF 0
  have hf1 := hF 1
  have hf2 := hF 2
  unfold logSecondNumerator
  simp_rw [pow_two]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_sub,iteratedDeriv_fun_mul,
    iteratedDeriv_fun_add,iteratedDeriv_const,iteratedDeriv_fun_id_zero,hD]
  interval_cases n <;> norm_num [Finset.sum_range_succ,Nat.choose,h0,h2,hg0]
  all_goals first | (ring; done) | linear_combination -8*(F 1 0)*hc

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.logSecondNumerator_derivatives_vanish
