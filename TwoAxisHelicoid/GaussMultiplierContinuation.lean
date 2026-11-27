import TwoAxisHelicoid.NullGaussLogSymmetry
import TwoAxisHelicoid.GaussMultiplierRigidity
import Mathlib.Analysis.Analytic.Uniqueness

namespace TwoAxisHelicoid
open Complex Set Metric Filter
open scoped Topology

theorem nullGauss_mul_height {p : Fin 3 → ℂ} (hp : ComplexNull p) (hn : p 2 ≠ 0) :
    nullGauss p * p 2 = -nullHorizontalPlus p ∧ (nullGauss p)⁻¹ * p 2 = nullHorizontalMinus p := by
  have hd := (null_horizontal_nonzero_of_height hp hn).1
  have h := null_horizontal_product hp
  unfold nullGauss
  constructor
  · field_simp
    linear_combination h
  · field_simp

/-- If two actual holomorphic null differentials have equal heights and Gauss
logarithmic derivatives, one complex multiplier relates their horizontal
coefficients on the whole connected domain, even at ordinary Gauss poles. -/
theorem horizontal_forms_of_equal_gauss_log {U : Set ℂ} (hU : IsOpen U) (hu : IsPreconnected U)
    {p q : ℂ → Fin 3 → ℂ} (hp : ∀ z ∈ U, ∀ j, AnalyticAt ℂ (fun w => p w j) z)
    (hq : ∀ z ∈ U, ∀ j, AnalyticAt ℂ (fun w => q w j) z)
    (hpn : ∀ z ∈ U, ComplexNull (p z)) (hqn : ∀ z ∈ U, ComplexNull (q z))
    (hh : ∀ z ∈ U, q z 2 = p z 2) {b : ℂ} (hb : b ∈ U) (hb' : p b 2 ≠ 0)
    (hl : ∀ z ∈ U, p z 2 ≠ 0 → deriv (nullGauss ∘ q) z/nullGauss (q z)
      = deriv (nullGauss ∘ p) z/nullGauss (p z)) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z ∈ U,
      nullHorizontalPlus (q z) = c*nullHorizontalPlus (p z) ∧
      nullHorizontalMinus (q z) = c⁻¹*nullHorizontalMinus (p z) := by
  obtain ⟨r,hr,hB⟩ := Metric.mem_nhds_iff.mp
    ((show ∀ᶠ z in 𝓝 b, z ∈ U from hU.mem_nhds hb).and ((hp b hb 2).continuousAt.eventually_ne hb'))
  have hn (z : ℂ) (hz : z ∈ ball b r) : q z 2 ≠ 0 := (hh z (hB hz).1).symm ▸ (hB hz).2
  obtain ⟨c,hc,he⟩ := equal_logarithmic_derivatives_constant_ratio (f := nullGauss ∘ p)
    (g := nullGauss ∘ q) isOpen_ball (convex_ball b r |>.isConnected ⟨b,mem_ball_self hr⟩)
    (fun z hz => (nullGauss_analyticAt_of_height (hp z (hB hz).1) (hpn z (hB hz).1) (hB hz).2).differentiableAt)
    (fun z hz => (nullGauss_analyticAt_of_height (hq z (hB hz).1) (hqn z (hB hz).1) (hn z hz)).differentiableAt)
    (fun z hz => nullGauss_ne_zero_of_height (hpn z (hB hz).1) (hB hz).2)
    (fun z hz => nullGauss_ne_zero_of_height (hqn z (hB hz).1) (hn z hz))
    (fun z hz => hl z (hB hz).1 (hB hz).2)
  have hhB (z : ℂ) (hz : z ∈ ball b r) :
      nullHorizontalPlus (q z) = c*nullHorizontalPlus (p z) ∧
      nullHorizontalMinus (q z) = c⁻¹*nullHorizontalMinus (p z) := by
    have ha := nullGauss_mul_height (hpn z (hB hz).1) (hB hz).2
    have hd := nullGauss_mul_height (hqn z (hB hz).1) (hn z hz)
    have e : nullGauss (q z) = c*nullGauss (p z) := he z hz
    rw [e,hh z (hB hz).1,mul_inv_rev] at hd
    exact ⟨by linear_combination hd.1-c*ha.1,by linear_combination c⁻¹*ha.2-hd.2⟩
  have a₁ (u : ℂ → Fin 3 → ℂ) (h : ∀ z ∈ U, ∀ j, AnalyticAt ℂ (fun w => u w j) z) :
      AnalyticOnNhd ℂ (nullHorizontalPlus ∘ u) U := fun z hz => (h z hz 0).add (analyticAt_const.mul (h z hz 1))
  have a₂ (u : ℂ → Fin 3 → ℂ) (h : ∀ z ∈ U, ∀ j, AnalyticAt ℂ (fun w => u w j) z) :
      AnalyticOnNhd ℂ (nullHorizontalMinus ∘ u) U := fun z hz => (h z hz 0).sub (analyticAt_const.mul (h z hz 1))
  have p₁ := (a₁ q hq).eqOn_of_preconnected_of_eventuallyEq
    (show AnalyticOnNhd ℂ (fun z => c*nullHorizontalPlus (p z)) U from fun z hz => analyticAt_const.mul (a₁ p hp z hz))
    hu hb ((show ∀ᶠ z in 𝓝 b, z ∈ ball b r from ball_mem_nhds b hr).mono fun z hz => (hhB z hz).1)
  have p₂ := (a₂ q hq).eqOn_of_preconnected_of_eventuallyEq
    (show AnalyticOnNhd ℂ (fun z => c⁻¹*nullHorizontalMinus (p z)) U from fun z hz => analyticAt_const.mul (a₂ p hp z hz))
    hu hb ((show ∀ᶠ z in 𝓝 b, z ∈ ball b r from ball_mem_nhds b hr).mono fun z hz => (hhB z hz).2)
  exact ⟨c,hc,fun _ hz => ⟨p₁ hz,p₂ hz⟩⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.horizontal_forms_of_equal_gauss_log
