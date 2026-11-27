import TwoAxisHelicoid.GenusOneCanonicalDivisor
import Mathlib.Geometry.Manifold.Complex
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff Manifold

/-- A nowhere vanishing holomorphic differential on a compact connected
Riemann surface spans the entire space of such differentials. -/
theorem nowhere_zero_section_spans {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] [CompactSpace M] [PreconnectedSpace M]
    (w : holomorphicCotangentSections M) (nw : ∀ x, w.1 x (chartAt ℂ x x)≠0)
    (v : holomorphicCotangentSections M) : ∃ c : ℂ, c • w=v := by
  let ratio := fun x => v.1 x (chartAt ℂ x x)/w.1 x (chartAt ℂ x x)
  have denominator (i x : M) (h : x∈(chartAt ℂ i).source) : w.1 i (chartAt ℂ i x)≠0 := by
    intro zero
    have atx := w.2.2.1 x i x ⟨mem_chart_source ℂ x,h⟩
    exact nw x (by simpa only [zero,zero_mul] using atx)
  have localRatio (i x : M) (h : x∈(chartAt ℂ i).source) :
      ratio x=v.1 i (chartAt ℂ i x)/w.1 i (chartAt ℂ i x) := by
    apply (div_eq_div_iff (nw x) (denominator i x h)).mpr
    rw [v.2.2.1 i x x ⟨h,mem_chart_source ℂ x⟩,w.2.2.1 i x x ⟨h,mem_chart_source ℂ x⟩]
    ring
  have hol : MDifferentiable 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ratio := by
    intro x
    let e := chartAt ℂ x
    have hx := mem_chart_source ℂ x
    have hq := (v.2.1 x (e x) (e.map_source hx)).div (w.2.1 x (e x) (e.map_source hx)) (nw x)
    have hc : MDifferentiableAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) e x := (mdifferentiable_chart x).mdifferentiableAt hx
    apply (hq.differentiableAt.comp_mdifferentiableAt hc).congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact localRatio x y hy
  obtain ⟨c,eq⟩ := hol.exists_eq_const_of_compactSpace
  refine ⟨c,Subtype.ext ?_⟩
  funext i z
  change c*w.1 i z=v.1 i z
  by_cases hz : z∈(chartAt ℂ i).target
  · let x := (chartAt ℂ i).symm z
    have hx := (chartAt ℂ i).map_target hz
    have val : chartAt ℂ i x=z := (chartAt ℂ i).right_inv hz
    have cr : ratio x=c := congrFun eq x
    have nd := denominator i x hx
    rw [localRatio i x hx,val] at cr
    rw [val] at nd
    exact ((div_eq_iff nd).mp cr).symm
  · rw [w.2.2.2 i z hz,v.2.2.2 i z hz,mul_zero]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.nowhere_zero_section_spans
