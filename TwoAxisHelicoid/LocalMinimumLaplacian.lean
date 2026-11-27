import TwoAxisHelicoid.AnalyticPlaneLaplacian
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace TwoAxisHelicoid
open Complex Filter Set Topology InnerProductSpace Laplacian
open scoped Topology InnerProductSpace

/-- Restriction of the real derivative on the parameter plane to a
straight line. -/
theorem parameter_line_hasDerivAt {f : ℂ → ℝ} {z v : ℂ} {t : ℝ}
    (hf : DifferentiableAt ℝ f (z+t • v)) :
    HasDerivAt (fun s : ℝ => f (z+s • v)) (planePartial v f (z+t • v)) t := by
  have dl : HasDerivAt (fun s : ℝ => z+s • v) v t := by
    simpa only [id_eq,one_smul] using! ((hasDerivAt_id t).smul_const v).const_add z
  exact hf.hasFDerivAt.comp_hasDerivAt t dl

theorem second_derivative_nonnegative_at_minimum {g : ℝ → ℝ} {t : ℝ}
    (hg : ContinuousAt g t) (hm : IsLocalMin g t) : 0 ≤ deriv (deriv g) t := by
  by_contra! hneg
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hm.deriv_eq_zero hg
  have he : g =ᶠ[𝓝 t] fun _ => g t :=
    (hm.and hmax).mono fun _ h => le_antisymm h.2 h.1
  have hzero : deriv (deriv g) t = 0 := by simpa using he.deriv.deriv_eq
  exact hneg.ne hzero

theorem analytic_plane_line_second_derivative {f : ℂ → ℝ} {z : ℂ}
    (hf : AnalyticAt ℝ f z) (v : ℂ) :
    deriv (deriv (fun t : ℝ => f (z+t • v))) 0 = planePartial v (planePartial v f) z := by
  let c := fun t : ℝ => z+t • v
  have c0 : c 0=z := by simp [c]
  have hc : Continuous c := by dsimp [c]; fun_prop
  have ha : ∀ᶠ t in 𝓝 (0:ℝ), AnalyticAt ℝ f (c t) :=
    hc.continuousAt (c0.symm ▸ hf.eventually_analyticAt)
  have h' : deriv (f ∘ c) =ᶠ[𝓝 (0:ℝ)] (planePartial v f) ∘ c := by
    filter_upwards [ha] with t ht using (parameter_line_hasDerivAt ht.differentiableAt).deriv
  have h'' := parameter_line_hasDerivAt (v := v) (z := z) (t := 0)
    (show DifferentiableAt ℝ (planePartial v f) (c 0) from c0.symm ▸ (planePartial_analyticAt hf v).differentiableAt)
  exact h'.deriv_eq.trans (h''.deriv.trans (congrArg (planePartial v (planePartial v f)) c0))

theorem analytic_plane_second_partial_nonnegative_at_minimum {f : ℂ → ℝ} {z : ℂ}
    (hf : AnalyticAt ℝ f z) (hm : IsLocalMin f z) (v : ℂ) :
    0 ≤ planePartial v (planePartial v f) z := by
  let c := fun t : ℝ => z+t • v
  have c0 : c 0=z := by simp [c]
  have hc : Continuous c := by dsimp [c]; fun_prop
  have hmin : IsLocalMin (f ∘ c) 0 := by
    change ∀ᶠ t in 𝓝 (0:ℝ), f (c 0) ≤ f (c t)
    rw [c0]
    have tend : Tendsto c (𝓝 0) (𝓝 z) := by simpa only [c0] using (hc.tendsto 0)
    exact tend.eventually hm
  have hcont : ContinuousAt (f ∘ c) 0 := (c0.symm ▸ hf.continuousAt).comp hc.continuousAt
  rw [← analytic_plane_line_second_derivative hf v]
  exact second_derivative_nonnegative_at_minimum hcont hmin

theorem analytic_plane_laplacian_nonnegative_at_minimum {f : ℂ → ℝ} {z : ℂ}
    (hf : AnalyticAt ℝ f z) (hm : IsLocalMin f z) : 0 ≤ (Δ f) z := by
  rw [laplacian_plane_partials hf]
  exact add_nonneg (analytic_plane_second_partial_nonnegative_at_minimum hf hm 1)
    (analytic_plane_second_partial_nonnegative_at_minimum hf hm I)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.analytic_plane_laplacian_nonnegative_at_minimum
