import TwoAxisHelicoid.HolomorphicSurfaceIdentity
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Circle

namespace TwoAxisHelicoid
open Complex Set Metric Filter Function Topology
open scoped Topology ContDiff Manifold

/-- Two holomorphic germs with the same modulus differ by a unique
unit constant, including at a common zero of any finite order. -/
theorem equal_modulus_holomorphic_germs {f g : ℂ → ℂ} {p : ℂ}
    (af : AnalyticAt ℂ f p) (ag : AnalyticAt ℂ g p)
    (modulus : ∀ᶠ z in 𝓝 p, ‖f z‖=‖g z‖) (non : ¬ (∀ᶠ z in 𝓝 p, g z=0)) :
    ∃! c : Circle, ∀ᶠ z in 𝓝 p, f z=(c:ℂ)*g z := by
  have near := af.eventually_analyticAt.and (ag.eventually_analyticAt.and modulus)
  obtain ⟨r,rp,sub⟩ := Metric.mem_nhds_iff.mp near
  let B := ball p r
  obtain ⟨w,hw,nz⟩ : ∃ w∈B, g w≠0 := by
    by_contra! no
    apply non
    filter_upwards [ball_mem_nhds p rp] with w hw using no w hw
  let H := fun w => f w/g w
  have unit : ‖H w‖=1 := by rw [show H w=f w/g w from rfl,norm_div,(sub hw).2.2,div_self (norm_ne_zero_iff.mpr nz)]
  let c : Circle := ⟨H w,mem_sphere_zero_iff_norm.mpr unit⟩
  have aw : AnalyticAt ℂ H w := (sub hw).1.div (sub hw).2.1 nz
  have mx : IsLocalMax (norm ∘ H) w := by
    filter_upwards [isOpen_ball.mem_nhds hw,(sub hw).2.1.continuousAt.eventually_ne nz] with t ht nzt
    change ‖f t/g t‖≤‖H w‖
    rw [unit,norm_div,(sub ht).2.2,div_self (norm_ne_zero_iff.mpr nzt)]
  have same := eventually_eq_of_isLocalMax_norm (aw.eventually_analyticAt.mono fun _ h => h.differentiableAt) mx
  have localEq : f =ᶠ[𝓝 w] fun z => (c:ℂ)*g z := by
    filter_upwards [same,(sub hw).2.1.continuousAt.eventually_ne nz] with z hz nzz
    exact (div_eq_iff nzz).mp hz
  have whole := (show AnalyticOnNhd ℂ f B from fun z hz => (sub hz).1).eqOn_of_preconnected_of_eventuallyEq
    (show AnalyticOnNhd ℂ (fun z => (c:ℂ)*g z) B from fun z hz => analyticAt_const.mul (sub hz).2.1)
    (convex_ball p r).isPreconnected hw localEq
  have atP : ∀ᶠ z in 𝓝 p, f z=(c:ℂ)*g z := by
    filter_upwards [ball_mem_nhds p rp] with z hz using whole hz
  refine ⟨c,atP,?_⟩
  intro d hd
  apply Subtype.ext
  by_contra ne
  apply non
  filter_upwards [hd,atP] with z h1 h2
  exact (mul_eq_zero.mp (show ((d:ℂ)-(c:ℂ))*g z=0 by rw [sub_mul,← h1,← h2,sub_self])).resolve_left (sub_ne_zero.mpr ne)

/-- The equality-of-moduli germ statement in the given atlas of an
abstract Riemann surface. -/
theorem equal_modulus_holomorphic_surface_germs {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {f g : M → ℂ} {p : M}
    (af : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f p) (ag : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω g p)
    (modulus : ∀ᶠ z in 𝓝 p, ‖f z‖=‖g z‖) (non : ¬ (∀ᶠ z in 𝓝 p, g z=0)) :
    ∃! c : Circle, ∀ᶠ z in 𝓝 p, f z=(c:ℂ)*g z := by
  let e := chartAt ℂ p
  have ps : p∈e.source := mem_chart_source ℂ p
  have inv := contMDiffAt_symm_of_mem_maximalAtlas (I:=𝓘(ℂ,ℂ)) (n:=ω) (IsManifold.chart_mem_maximalAtlas p) (e.map_source ps)
  have left := e.left_inv ps
  have back : Tendsto e.symm (𝓝 (e p)) (𝓝 p) := by
    simpa only [left] using (e.symm.continuousAt (e.map_source ps)).tendsto
  have localF := (show ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f (e.symm (e p)) from left.symm ▸ af).comp (e p) inv
  have localG := (show ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω g (e.symm (e p)) from left.symm ▸ ag).comp (e p) inv
  have n : ¬ (∀ᶠ z in 𝓝 (e p), (g ∘ e.symm) z=0) := by
    intro no
    apply non
    filter_upwards [(e.continuousAt ps).eventually no,e.open_source.mem_nhds ps] with w h hw
    simpa [comp_apply,e.left_inv hw] using h
  obtain ⟨c,hc,only⟩ := equal_modulus_holomorphic_germs localF.contDiffAt.analyticAt localG.contDiffAt.analyticAt
    (back.eventually modulus) n
  refine ⟨c,?_,fun d hd => only d (back.eventually hd)⟩
  filter_upwards [(e.continuousAt ps).eventually hc,e.open_source.mem_nhds ps] with z hz hs
  simpa only [comp_apply,e.left_inv hs] using hz

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.equal_modulus_holomorphic_surface_germs
