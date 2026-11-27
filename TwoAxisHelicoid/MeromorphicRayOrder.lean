import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Complex Filter Bornology
open scoped Topology

private theorem eventually_norm_bound_of_limit {α : Type*} {l : Filter α} {f : α → ℂ} {b : ℂ}
    (limit : Tendsto f l (𝓝 b)) : ∀ᶠ a in l, ‖f a‖≤‖b‖+1 :=
  (limit.norm.eventually (gt_mem_nhds (lt_add_one ‖b‖))).mono fun _ h => h.le

theorem simple_pole_norm_times_radius_bounded {H : ℂ → ℂ} (mer : MeromorphicAt H 0)
    (order : meromorphicOrderAt H 0=((-1:ℤ):WithTop ℤ)) :
    ∃ C : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖z‖*‖H z‖≤C := by
  let J := (id : ℂ → ℂ)*H
  have m : MeromorphicAt J 0 := analyticAt_id.meromorphicAt.mul mer
  have o : 0≤meromorphicOrderAt J 0 := by
    rw [show meromorphicOrderAt J 0=_ from meromorphicOrderAt_mul analyticAt_id.meromorphicAt mer,
      meromorphicOrderAt_id,order]; norm_num
  obtain ⟨b,limit⟩ := (tendsto_nhds_iff_meromorphicOrderAt_nonneg m).mpr o
  exact ⟨‖b‖+1,(eventually_norm_bound_of_limit limit).mono fun z h => by simpa only [J,Pi.mul_apply,id_eq,norm_mul] using h⟩

/-- A meromorphic function escaping to infinity along one approach to
zero has a simple pole if its norm times the radius is bounded on
that same approach. No bound in the other directions is needed. -/
theorem meromorphic_order_simple_of_ray {α : Type*} {l : Filter α} [l.NeBot] {p : α → ℂ}
    (limit : Tendsto p l (𝓝[≠] 0)) {F : ℂ → ℂ} (mer : MeromorphicAt F 0)
    (esc : Tendsto (fun a => ‖F (p a)‖) l atTop)
    (bound : ∃ B : ℝ, ∀ᶠ a in l, ‖p a‖*‖F (p a)‖≤B) :
    meromorphicOrderAt F 0=((-1:ℤ):WithTop ℤ) := by
  have neg : meromorphicOrderAt F 0<0 := by
    by_contra! ge
    obtain ⟨b,conv⟩ := (tendsto_nhds_iff_meromorphicOrderAt_nonneg mer).mpr ge
    obtain ⟨a,low,high⟩ := ((eventually_norm_bound_of_limit (conv.comp limit)).and (esc.eventually_gt_atTop (‖b‖+1))).exists
    exact high.not_ge low
  let J := (id : ℂ → ℂ)*F
  have ge : 0≤meromorphicOrderAt J 0 := by
    by_contra! neg
    obtain ⟨B,bd⟩ := bound
    have grow := (tendsto_norm_cobounded_atTop.comp (tendsto_cobounded_of_meromorphicOrderAt_neg neg)).comp limit
    obtain ⟨a,lo,hi⟩ := (bd.and (grow.eventually_gt_atTop B)).exists
    exact hi.not_ge (by simpa only [Function.comp_apply,J,Pi.mul_apply,id_eq,norm_mul] using lo)
  obtain ⟨n,hn⟩ := WithTop.ne_top_iff_exists.mp neg.ne_top
  rw [show meromorphicOrderAt J 0=_ from meromorphicOrderAt_mul analyticAt_id.meromorphicAt mer,
    meromorphicOrderAt_id,← hn] at ge
  rw [← hn] at neg ⊢
  have gt : n<0 := by exact_mod_cast neg
  have lb : 0≤1+n := by exact_mod_cast ge
  have h : n= -1 := by omega
  rw [h]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.meromorphic_order_simple_of_ray
