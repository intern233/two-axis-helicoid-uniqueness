import TwoAxisHelicoid.TorusHeightFlux
import TwoAxisHelicoid.PuncturedTorusPolygon

namespace TwoAxisHelicoid
open Complex Set

/-- Pull a function on the punctured torus back to its covering plane,
with the zero value reserved for the missing lattice. -/
noncomputable def puncturedTorusPullback {V : Type*} [Zero V] (L : PeriodPair)
    (X : PuncturedPeriodTorus L → V) (z : ℂ) : V := by
  classical
  exact if hz : z ∉ L.lattice then X (puncturedPlaneProjection L ⟨z,hz⟩) else 0

theorem puncturedTorusPullback_periodic {V : Type*} [Zero V] (L : PeriodPair)
    (X : PuncturedPeriodTorus L → V) (z ω : ℂ) (hω : ω ∈ L.lattice) :
    puncturedTorusPullback L X (z+ω) = puncturedTorusPullback L X z := by
  by_cases hz : z ∈ L.lattice
  · simp [puncturedTorusPullback,hz,L.lattice.add_mem hz hω]
  · have hz' : z+ω ∉ L.lattice := fun h => hz (by simpa using L.lattice.sub_mem h hω)
    simp only [puncturedTorusPullback,dite_eq_left hz,dite_eq_left hz']
    exact congrArg X (Subtype.ext (periodTorusProjection_add_lattice L z ω hω))

theorem TorusPeriodPolygon.height_period_re_zero {L : PeriodPair} (γ : TorusPeriodPolygon L)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (L.lattice : Set ℂ)ᶜ)
    {H : ℂ → ℝ} (hH : ∀ z ∉ L.lattice, HasFDerivAt H (realCoefficientDerivative (f z)) z)
    (hper : ∀ z ω, ω ∈ L.lattice → H (z+ω) = H z) : (γ.edges.integral f).re = 0 := by
  have h := γ.edges.real_integral_eq_height_difference hf hH
  have he := hper γ.start (γ.finish-γ.start) γ.closed
  rw [add_sub_cancel] at he
  rw [h,he,sub_self]

/-- Appendix C.2, with an actual closed polygonal path in the punctured
torus. Its nonzero flux is the sum of the complex integrals on its lifted
edges. Single-valued height is used to deduce zero real periods. -/
theorem single_valued_height_nonzero_torus_flux (L : PeriodPair) (H : PuncturedPeriodTorus L → ℝ)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (L.lattice : Set ℂ)ᶜ)
    (hp : ∀ z ω, ω ∈ L.lattice → f (z+ω) = f z)
    (hm : MeromorphicAt f 0) (ho : meromorphicOrderAt f 0 = (-2 : ℤ))
    (hH : ∀ z ∉ L.lattice, HasFDerivAt (puncturedTorusPullback L H)
      (realCoefficientDerivative (f z)) z) :
    ∃ γ : TorusPeriodPolygon L, (γ.edges.integral f).im ≠ 0 := by
  obtain ⟨x,y,p,hw,hn⟩ := torus_height_exists_nonzero_imaginary_period L hf hp hm ho
    (fun {x y} p h => (TorusPeriodPolygon.mk x y p h).height_period_re_zero hf hH
      (puncturedTorusPullback_periodic L H))
  exact ⟨⟨x,y,p,hw⟩,hn⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.single_valued_height_nonzero_torus_flux
