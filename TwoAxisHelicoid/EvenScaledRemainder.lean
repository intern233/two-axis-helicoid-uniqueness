import TwoAxisHelicoid.EvenTaylorFourth
import Mathlib.Analysis.Asymptotics.Lemmas

namespace TwoAxisHelicoid
open Filter
open scoped Topology

theorem even_analytic_scaled_remainder {α : Type*} {l : Filter α} [l.NeBot]
    {f : ℝ → ℝ} {x d : α → ℝ} {k s : ℝ}
    (hf : AnalyticAt ℝ f 0) (he : (fun y : ℝ => f (-y)) =ᶠ[𝓝 0] f)
    (hx : Tendsto x l (𝓝 0)) (hk : Tendsto (fun t => x t^2/d t) l (𝓝 k))
    (hkn : k ≠ 0) (hdn : ∀ᶠ t in l, d t ≠ 0)
    (hs : Tendsto (fun t => (f (x t)-f 0)/d t) l (𝓝 s)) :
    ∃ r : ℝ, Tendsto (fun t => (f (x t)-f 0-(s/k)*x t^2)/d t^2) l (𝓝 r) := by
  obtain ⟨c,R,hR,hrem⟩ := even_analytic_fourth_decomposition hf he
  have hr : Tendsto (fun t => R (x t)) l (𝓝 (R 0)) := hR.continuousAt.tendsto.comp hx
  have hq : Tendsto (fun t => x t^2) l (𝓝 (0:ℝ)) := by simpa using hx.pow 2
  have hh : Tendsto (fun t => (c+x t^2*R (x t))*(x t^2/d t)) l (𝓝 (c*k)) := by
    simpa only [zero_mul,add_zero] using (tendsto_const_nhds.add (hq.mul hr)).mul hk
  have heq : (fun t => (c+x t^2*R (x t))*(x t^2/d t)) =ᶠ[l]
      fun t => (f (x t)-f 0)/d t := by
    filter_upwards [hx.eventually hrem,hdn] with t ht hd
    rw [ht]
    field_simp
    ring
  have hck : c*k = s := tendsto_nhds_unique (hh.congr' heq) hs
  have hc : c = s/k := (eq_div_iff hkn).mpr hck
  refine ⟨k^2*R 0,?_⟩
  have hlast := (hk.pow 2).mul hr
  apply hlast.congr'
  filter_upwards [hx.eventually hrem,hdn] with t ht hd
  rw [ht,← hc]
  field_simp
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.even_analytic_scaled_remainder
