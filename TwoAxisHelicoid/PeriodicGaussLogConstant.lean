import TwoAxisHelicoid.GaussMultiplierContinuation
import TwoAxisHelicoid.PeriodicHeightRigidity
import TwoAxisHelicoid.PeriodTorusTopology

namespace TwoAxisHelicoid
open Complex Set Metric Filter
open scoped Topology

/-- Once the two logarithmic Gauss derivatives differ by a constant, their
nonzero Gauss data and the two genuine torus periods force that constant
to vanish. This uses only one regular disk; the analytic horizontal
coefficients carry the identity through ordinary Gauss zeros and poles. -/
theorem torus_gauss_log_constant_vanishes (L : PeriodPair) {p q : ℂ → Fin 3 → ℂ}
    (hp : ∀ z ∉ L.lattice, ∀ j, AnalyticAt ℂ (fun w => p w j) z)
    (hq : ∀ z ∉ L.lattice, ∀ j, AnalyticAt ℂ (fun w => q w j) z)
    (hpn : ∀ z ∉ L.lattice, ComplexNull (p z)) (hqn : ∀ z ∉ L.lattice, ComplexNull (q z))
    (hper : ∀ z ω, ω ∈ L.lattice → z ∉ L.lattice →
      p (z+ω) = p z ∧ q (z+ω) = q z)
    (hh : ∀ z ∉ L.lattice, q z 2 = p z 2) {b d : ℂ} (hb : b ∉ L.lattice) (hb' : p b 2 ≠ 0)
    (hlog : ∀ᶠ z in 𝓝 b, deriv (nullGauss ∘ q) z/nullGauss (q z)
      -deriv (nullGauss ∘ p) z/nullGauss (p z) = d) : d = 0 := by
  let U := (L.lattice : Set ℂ)ᶜ
  obtain ⟨r,hr,hB⟩ := Metric.mem_nhds_iff.mp
    ((show ∀ᶠ z in 𝓝 b, z ∈ U from L.isClosed_lattice.isOpen_compl.mem_nhds hb).and
      (((hp b hb 2).continuousAt.eventually_ne hb').and hlog))
  let T := fun z => exp (d*z)*nullGauss (p z)
  have hE (z : ℂ) : HasDerivAt (fun w => exp (d*w)) (exp (d*z)*d) z := by
    simpa using ((hasDerivAt_id z).const_mul d).cexp
  have hp' (z : ℂ) (hz : z ∈ ball b r) : DifferentiableAt ℂ (nullGauss ∘ p) z :=
    (nullGauss_analyticAt_of_height (hp z (hB hz).1) (hpn z (hB hz).1) (hB hz).2.1).differentiableAt
  have hp0 (z : ℂ) (hz : z ∈ ball b r) : nullGauss (p z) ≠ 0 :=
    nullGauss_ne_zero_of_height (hpn z (hB hz).1) (hB hz).2.1
  have hq0 (z : ℂ) (hz : z ∈ ball b r) : q z 2 ≠ 0 := (hh z (hB hz).1).symm ▸ (hB hz).2.1
  have hT (z : ℂ) (hz : z ∈ ball b r) := (hE z).mul (hp' z hz).hasDerivAt
  obtain ⟨c,hc,he⟩ := equal_logarithmic_derivatives_constant_ratio (f := T) (g := nullGauss ∘ q)
    isOpen_ball (convex_ball b r |>.isConnected ⟨b,mem_ball_self hr⟩)
    (fun z hz => (hT z hz).differentiableAt)
    (fun z hz => (nullGauss_analyticAt_of_height (hq z (hB hz).1) (hqn z (hB hz).1) (hq0 z hz)).differentiableAt)
    (fun z hz => mul_ne_zero (exp_ne_zero _) (hp0 z hz))
    (fun z hz => nullGauss_ne_zero_of_height (hqn z (hB hz).1) (hq0 z hz)) (by
      intro z hz
      have h := (hB hz).2.2
      have ht : deriv T z = exp (d*z)*d*nullGauss (p z) + exp (d*z)*deriv (nullGauss ∘ p) z := (hT z hz).deriv
      rw [ht]
      change _ = _ / (exp (d*z)*nullGauss (p z))
      rw [show (exp (d*z)*d*nullGauss (p z)+exp (d*z)*deriv (nullGauss ∘ p) z)/(exp (d*z)*nullGauss (p z)) =
        d+deriv (nullGauss ∘ p) z/nullGauss (p z) by field_simp [exp_ne_zero, hp0 z hz]]
      simpa only [Function.comp_apply] using (sub_eq_iff_eq_add.mp h))
  have hnear : (nullHorizontalPlus ∘ q) =ᶠ[𝓝 b] fun z => c*exp (d*z)*nullHorizontalPlus (p z) := by
    filter_upwards [ball_mem_nhds b hr] with z hz
    have h₁ := (nullGauss_mul_height (hpn z (hB hz).1) (hB hz).2.1).1
    have h₂ := (nullGauss_mul_height (hqn z (hB hz).1) (hq0 z hz)).1
    have e : nullGauss (q z) = c*(exp (d*z)*nullGauss (p z)) := he z hz
    rw [e,hh z (hB hz).1] at h₂
    change nullHorizontalPlus (q z) = _
    linear_combination h₂-c*exp (d*z)*h₁
  have ha {u : ℂ → Fin 3 → ℂ} (h : ∀ z ∉ L.lattice, ∀ j, AnalyticAt ℂ (fun w => u w j) z) :
      AnalyticOnNhd ℂ (nullHorizontalPlus ∘ u) U :=
    fun z hz => (h z hz 0).add (analyticAt_const.mul (h z hz 1))
  have hall := (ha hq).eqOn_of_preconnected_of_eventuallyEq
    (show AnalyticOnNhd ℂ (fun z => c*exp (d*z)*nullHorizontalPlus (p z)) U from
      fun z hz => (analyticAt_const.mul ((analyticAt_const.mul analyticAt_id).cexp)).mul (ha hp z hz))
    (marked_torus_lattice_complement_connected L).isPreconnected hb hnear
  apply complex_eq_zero_of_lattice_real_periods L
  intro ω hω
  have hbω : b+ω ∉ L.lattice := fun h => hb (by simpa using L.lattice.sub_mem h hω)
  have h₁ := hall hb
  have h₂ := hall hbω
  change nullHorizontalPlus (q (b+ω)) = c*exp (d*(b+ω))*nullHorizontalPlus (p (b+ω)) at h₂
  change nullHorizontalPlus (q b) = c*exp (d*b)*nullHorizontalPlus (p b) at h₁
  rw [(hper b ω hω hb).1,(hper b ω hω hb).2,h₁,mul_add,exp_add] at h₂
  have hee : exp (d*ω) = 1 := by
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hc (exp_ne_zero (d*b)))
      (null_horizontal_nonzero_of_height (hpn b hb) hb').2)
    linear_combination -h₂
  have hnorm := congrArg (fun v : ℂ => ‖v‖) hee
  rw [norm_exp,norm_one,Real.exp_eq_one_iff] at hnorm
  rwa [mul_comm]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.torus_gauss_log_constant_vanishes
