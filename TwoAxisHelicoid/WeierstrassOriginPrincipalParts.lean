module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace TwoAxisHelicoid
open Filter
open scoped Topology

/-- For any lattice, the regular part of ℘ begins with (g₂/20)z².
The normalized negative primitive of its regular part begins with
−(g₂/60)z³. The two remainders are analytic at the origin. -/
theorem weierstrass_normalized_primitive_laurent (L : PeriodPair) {R : ℂ → ℂ}
    (analytic : AnalyticAt ℂ R 0) (zero : R 0 = 0)
    (derivative : deriv R =ᶠ[𝓝 0] fun z => -L.weierstrassPExcept 0 z) :
    ∃ A B : ℂ → ℂ, AnalyticAt ℂ A 0 ∧ AnalyticAt ℂ B 0 ∧
      (∀ᶠ z in 𝓝 0, L.weierstrassP z = z⁻¹^2 + (L.g₂/20)*z^2 + z^4*A z) ∧
      (∀ᶠ z in 𝓝 0, R z = -(L.g₂/60)*z^3 + z^5*B z) := by
  have jet (n : ℕ) : iteratedDeriv (n+1) R 0 =
      -iteratedDeriv n (L.weierstrassPExcept 0) 0 := by
    rw [iteratedDeriv_succ', derivative.iteratedDeriv_eq]
    exact iteratedDeriv_fun_neg n _ _
  have j1 : iteratedDeriv 1 R 0 = -iteratedDeriv 0 (L.weierstrassPExcept 0) 0 := jet 0
  have j2 : iteratedDeriv 2 R 0 = -iteratedDeriv 1 (L.weierstrassPExcept 0) 0 := jet 1
  have j3 : iteratedDeriv 3 R 0 = -iteratedDeriv 2 (L.weierstrassPExcept 0) 0 := jet 2
  have j4 : iteratedDeriv 4 R 0 = -iteratedDeriv 3 (L.weierstrassPExcept 0) 0 := jet 3
  obtain ⟨A, ha, wp⟩ := (L.analyticAt_weierstrassPExcept 0).exists_eventuallyEq_sum_add_pow_mul 4
  obtain ⟨B, hb, primitive⟩ := analytic.exists_eventuallyEq_sum_add_pow_mul 5
  refine ⟨A, B, ha, hb, ?_, ?_⟩
  · filter_upwards [wp] with z hz
    have pole : L.weierstrassP z = z⁻¹^2 + L.weierstrassPExcept 0 z := by
      simpa [one_div, inv_pow, add_comm] using (L.weierstrassPExcept_add 0 z).symm
    norm_num [Finset.sum_range_succ, PeriodPair.iteratedDeriv_weierstrassPExcept_self,
      L.G_eq_zero_of_odd 3 (by decide), L.G_eq_zero_of_odd 5 (by decide),
      Nat.factorial, smul_eq_mul] at hz
    rw [pole, hz, PeriodPair.g₂]
    ring
  · filter_upwards [primitive] with z hz
    norm_num [Finset.sum_range_succ, j1, j2, j3, j4, iteratedDeriv_zero, zero,
      PeriodPair.iteratedDeriv_weierstrassPExcept_self, L.G_eq_zero_of_odd 3 (by decide),
      L.G_eq_zero_of_odd 5 (by decide), Nat.factorial, smul_eq_mul] at hz
    rw [hz, PeriodPair.g₂]
    ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.weierstrass_normalized_primitive_laurent
