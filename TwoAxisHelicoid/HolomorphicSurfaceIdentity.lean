import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic

namespace TwoAxisHelicoid
open Complex Set Filter Function Topology Metric
open scoped Topology ContDiff Manifold

/-- Holomorphic continuation of a constant germ in the intrinsic
complex atlas of any connected Riemann surface. -/
theorem holomorphic_surface_constant_of_germ {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] [PreconnectedSpace M] {f : M → ℂ}
    (hol : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f) {p : M} {b : ℂ}
    (germ : ∀ᶠ y in 𝓝 p, f y=b) : ∀ x, f x=b := by
  let S := interior {y : M | f y=b}
  have closed : IsClosed S := by
    apply isClosed_of_closure_subset
    intro x hx
    let e := chartAt ℂ x
    have xs : x∈e.source := mem_chart_source ℂ x
    have xt := e.map_source xs
    obtain ⟨r,rp,sub⟩ := Metric.isOpen_iff.mp e.open_target (e x) xt
    let V := ball (e x) r
    have vn : V∈𝓝 (e x) := ball_mem_nhds _ rp
    have near : ∀ᶠ y in 𝓝 x, y∈e.source ∧ e y∈V := by
      filter_upwards [e.open_source.mem_nhds xs,(e.continuousAt xs).eventually vn] with y ys yv using ⟨ys,yv⟩
    obtain ⟨y,⟨ys,yv⟩,hy⟩ := mem_closure_iff_nhds.mp hx _ near
    have fy : ∀ᶠ t in 𝓝 y, f t=b := mem_interior_iff_mem_nhds.mp hy
    have an : AnalyticOnNhd ℂ (f ∘ e.symm) V := fun w hw =>
      ((hol (e.symm w)).comp w (contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,ℂ)) x) (sub hw))).contDiffAt.analyticAt
    have atY : (f ∘ e.symm) =ᶠ[𝓝 (e y)] fun _ => b := by
      have h : Tendsto e.symm (𝓝 (e y)) (𝓝 (e.symm (e y))) := (e.symm.continuousAt (e.map_source ys)).tendsto
      rw [e.left_inv ys] at h
      exact h.eventually fy
    have eq := an.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const (convex_ball _ _).isPreconnected yv atY
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [near] with t ht
    exact (congrArg f (e.left_inv ht.1)).symm.trans (eq ht.2)
  have allS := (isClopen_iff.mp (show IsClopen S from ⟨closed,isOpen_interior⟩)).resolve_left
    (show S.Nonempty from ⟨p,mem_interior_iff_mem_nhds.mpr germ⟩).ne_empty
  intro x
  exact interior_subset (s:={y : M | f y=b}) (show x∈S from allS.symm ▸ mem_univ x)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.holomorphic_surface_constant_of_germ
