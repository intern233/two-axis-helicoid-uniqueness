import TwoAxisHelicoid.TorusHeightFluxLoop
import TwoAxisHelicoid.HarmonicComplexCoefficient

namespace TwoAxisHelicoid
open Complex InnerProductSpace

/-- The height differential computed from a single-valued harmonic height
has a nonzero handle flux whenever its unique puncture is a double pole. -/
theorem harmonic_punctured_torus_has_nonzero_height_flux (L : PeriodPair)
    (H : PuncturedPeriodTorus L → ℝ)
    (hh : ∀ z ∉ L.lattice, HarmonicAt (puncturedTorusPullback L H) z)
    (hm : MeromorphicAt (scalarComplexCoefficient (puncturedTorusPullback L H)) 0)
    (ho : meromorphicOrderAt (scalarComplexCoefficient (puncturedTorusPullback L H)) 0 = (-2 : ℤ)) :
    ∃ γ : TorusPeriodPolygon L,
      (γ.edges.integral (scalarComplexCoefficient (puncturedTorusPullback L H))).im ≠ 0 := by
  let h := puncturedTorusPullback L H
  apply single_valued_height_nonzero_torus_flux L H
    (fun z hz => scalarComplexCoefficient_analyticAt (hh z hz)) _ hm ho
    (fun z hz => scalarComplexCoefficient_hasFDerivAt ((hh z hz).1.differentiableAt two_ne_zero))
  intro z ω hω
  have e : (fun w => h (w+ω)) = h := funext (fun w => puncturedTorusPullback_periodic L H w ω hω)
  have he := fderiv_comp_add_right (𝕜 := ℝ) (f := h) (x := z) ω
  rw [e] at he
  change scalarComplexCoefficient h (z+ω) = scalarComplexCoefficient h z
  unfold scalarComplexCoefficient
  rw [he]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_punctured_torus_has_nonzero_height_flux
