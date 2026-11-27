import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

namespace TwoAxisHelicoid
open Complex Filter Topology
open scoped Topology

/-- A holomorphic solution of h''=P h with both initial values zero
vanishes near the initial point. The recurrence raises the order of the
zero by two. -/
theorem analytic_second_order_zero_germ {h P : ℂ → ℂ} {z : ℂ}
    (hh : AnalyticAt ℂ h z) (hP : AnalyticAt ℂ P z) (h₀ : h z = 0) (h₁ : deriv h z = 0)
    (h₂ : deriv (deriv h) =ᶠ[𝓝 z] fun w => P w*h w) :
    ∀ᶠ w in 𝓝 z, h w = 0 := by
  apply analyticOrderAt_eq_top.mp
  apply ENat.eq_top_iff_forall_ge.mpr
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have prod : analyticOrderAt h z ≤ analyticOrderAt (deriv (deriv h)) z := by
      rw [analyticOrderAt_congr h₂]
      change _ ≤ analyticOrderAt (P • h) z
      rw [analyticOrderAt_smul hP hh]
      exact le_add_self
    have step := (analyticOrderAt_deriv_ge_iff hh.deriv h₁).mp (ih.trans prod)
    have hn : (n:ℕ∞) ≤ analyticOrderAt (deriv h) z := (le_self_add.trans step)
    simpa only [Nat.cast_add_one] using (analyticOrderAt_deriv_ge_iff hh h₀).mp hn

/-- Two analytic solutions of the Weierstrass second-order equation are
determined by their value and first derivative at any ordinary point,
including a zero of the first derivative. -/
theorem analytic_quadratic_ode_germ_unique {f g : ℂ → ℂ} {A B z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (ef : deriv (deriv f) =ᶠ[𝓝 z] fun w => A*(f w)^2+B)
    (eg : deriv (deriv g) =ᶠ[𝓝 z] fun w => A*(g w)^2+B)
    (e₀ : f z = g z) (e₁ : deriv f z = deriv g z) : f =ᶠ[𝓝 z] g := by
  let h := fun w => f w-g w
  have eh : deriv h =ᶠ[𝓝 z] fun w => deriv f w-deriv g w := by
    filter_upwards [hf.eventually_analyticAt,hg.eventually_analyticAt] with w hw hv
    exact (hw.differentiableAt.hasDerivAt.sub hv.differentiableAt.hasDerivAt).deriv
  have diff : deriv (deriv h) =ᶠ[𝓝 z] fun w => (A*(f w+g w))*h w := by
    filter_upwards [eh.deriv,ef,eg,hf.deriv.eventually_analyticAt,hg.deriv.eventually_analyticAt] with w hw hf' hg' hf'' hg''
    have e : deriv (deriv h) w = deriv (deriv f) w-deriv (deriv g) w := hw.trans
      (hf''.differentiableAt.hasDerivAt.sub hg''.differentiableAt.hasDerivAt).deriv
    rw [e,hf',hg']
    dsimp [h]
    ring
  have van := analytic_second_order_zero_germ (hf.sub hg) (analyticAt_const.mul (hf.add hg))
    (sub_eq_zero.mpr e₀) (eh.self_of_nhds.trans (sub_eq_zero.mpr e₁)) diff
  filter_upwards [van] with w hw using sub_eq_zero.mp hw

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.analytic_quadratic_ode_germ_unique
