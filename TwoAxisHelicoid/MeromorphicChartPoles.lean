import TwoAxisHelicoid.CompactIsolatedPoles
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Complex.Basic

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology

/-- Meromorphy in local coordinates forces the intrinsic pole locus to be
finite on a compact complex curve. `hP` identifies a pole as a point where
the coefficient is nonanalytic in every coordinate chart containing it. -/
theorem meromorphic_chart_poles_finite {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [CompactSpace X] {F : X → ℂ → ℂ} {P : Set X}
    (hF : ∀ p : X, MeromorphicAt (F p) (chartAt ℂ p p))
    (hP : ∀ p x : X, x ∈ (chartAt ℂ p).source → x ∈ P →
      ¬ AnalyticAt ℂ (F p) (chartAt ℂ p x)) : P.Finite := by
  apply finite_of_locally_isolated_poles
  intro p
  have he := (hF p).eventually_analyticAt
  rw [eventually_nhdsWithin_iff] at he
  have hc := ((chartAt ℂ p).continuousAt (mem_chart_source ℂ p)).eventually he
  have hloc : ∀ᶠ x in 𝓝 p, x ∈ P → x = p := by
    filter_upwards [hc,chart_source_mem_nhds ℂ p] with x hx hxS
    intro hxP
    by_contra hxp
    apply hP p x hxS hxP
    apply hx
    intro heq
    exact hxp ((chartAt ℂ p).injOn hxS (mem_chart_source ℂ p) heq)
  obtain ⟨U,hU,hopen,hp⟩ := mem_nhds_iff.mp hloc
  exact ⟨U,hopen,hp,fun x hx hxP => hU hx hxP⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.meromorphic_chart_poles_finite
