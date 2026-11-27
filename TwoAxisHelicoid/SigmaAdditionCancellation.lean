import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

namespace TwoAxisHelicoid

noncomputable def sigmaAdditionNumerator (f u v g : ℂ → ℂ) (d z : ℂ) : ℂ :=
  (u z*v z/d^2)*z^2+g z*(f z)^2*z^2+(f z)^2

attribute [local fun_prop] AnalyticAt.contDiffAt in
theorem sigmaAdditionNumerator_derivatives_vanish
    (f u v g : ℂ → ℂ) (d e k p : ℂ)
    (hf : AnalyticAt ℂ f 0) (hu : AnalyticAt ℂ u 0) (hv : AnalyticAt ℂ v 0)
    (hg : AnalyticAt ℂ g 0) (hd : d ≠ 0)
    (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1) (hf2 : iteratedDeriv 2 f 0 = 0)
    (hf3 : iteratedDeriv 3 f 0 = 0)
    (hu0 : u 0 = -d) (hv0 : v 0 = d) (hu1 : deriv u 0 = e) (hv1 : deriv v 0 = e)
    (hu2 : iteratedDeriv 2 u 0 = -k) (hv2 : iteratedDeriv 2 v 0 = k)
    (hg0 : g 0 = -p) (hc : e^2-k*d = p*d^2) {n : ℕ} (hn : n < 5) :
    iteratedDeriv n (sigmaAdditionNumerator f u v g d) 0 = 0 := by
  unfold sigmaAdditionNumerator
  simp_rw [pow_two]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_add,iteratedDeriv_fun_mul,
    iteratedDeriv_div_const,iteratedDeriv_fun_id_zero]
  interval_cases n <;> norm_num [Finset.sum_range_succ,Nat.choose,iteratedDeriv_one,
    hf0,hf1,hf2,hf3,hu0,hv0,hu1,hv1,hu2,hv2,hg0,hd]
  all_goals field_simp [hd]
  all_goals first | (ring; done) | linear_combination 24*hc

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.sigmaAdditionNumerator_derivatives_vanish
