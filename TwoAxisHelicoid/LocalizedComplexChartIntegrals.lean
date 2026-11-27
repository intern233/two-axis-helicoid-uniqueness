import TwoAxisHelicoid.ComplexCurveStokesOverlap

namespace TwoAxisHelicoid
open Complex MeasureTheory Filter Set Topology Function
open scoped Topology ContDiff

/-- Multiplying a one-form by a cutoff supported in the second chart
and its derivative by a weight supported in the first chart allows both
integrals to run over the entire respective coordinate domains. -/
theorem localized_form_chart_integrals {M : Type*} [TopologicalSpace M]
    (e d : OpenPartialHomeomorph M ℂ) (a b : ℂ → ℂ) (weight cut : M → ℝ)
    (first : tsupport weight⊆e.source) (second : tsupport cut⊆d.source)
    (hol : ∀ z∈(e.symm.trans d).source, AnalyticAt ℂ (e.symm.trans d) z)
    (coeff : ∀ z∈(e.symm.trans d).source, a z=b ((e.symm.trans d) z)*deriv (e.symm.trans d) z)
    (reg : ∀ z∈d.target, DifferentiableAt ℝ b z)
    (dc : ∀ z∈d.target, DifferentiableAt ℝ (fun w => (cut (d.symm w):ℂ)) z) :
    (∫ z in e.target, weight (e.symm z) • complexFormExteriorCoefficient (fun w => (cut (e.symm w):ℂ)*a w) z)=
      ∫ z in d.target, weight (d.symm z) • complexFormExteriorCoefficient (fun w => (cut (d.symm w):ℂ)*b w) z := by
  let u := e.symm.trans d
  let A := fun z => (cut (e.symm z):ℂ)*a z
  let B := fun z => (cut (d.symm z):ℂ)*b z
  have compat (z : ℂ) (hz : z∈u.source) : A z=B (u z)*deriv u z := by
    have eq : d.symm (u z)=e.symm z := d.left_inv hz.2
    dsimp only [A,B]
    rw [eq,coeff z hz,mul_assoc]
  have db (z : ℂ) (hz : z∈u.source) : DifferentiableAt ℝ B (u z) :=
    (dc _ (d.map_source hz.2)).mul (reg _ (d.map_source hz.2))
  have middle := complex_form_integral_on_overlap e d A B weight u.open_source.measurableSet
    (Subset.rfl : u.source⊆u.source) hol compat db
  rw [show (e.symm.trans d) '' u.source=u.target from u.image_source_eq_target] at middle
  change (∫ z in e.target, weight (e.symm z) • complexFormExteriorCoefficient A z)=
    ∫ z in d.target, weight (d.symm z) • complexFormExteriorCoefficient B z
  calc
    _=(∫ z in u.source, weight (e.symm z) • complexFormExteriorCoefficient A z) := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero e.open_target.measurableSet (fun z hz => hz.1)
      intro z hz
      have absent : e.symm z∉tsupport cut := fun h => hz.2 ⟨hz.1,second h⟩
      have germ : A =ᶠ[𝓝 z] 0 := by
        filter_upwards [(e.continuousAt_symm hz.1).eventually (notMem_tsupport_iff_eventuallyEq.mp absent)] with w hw
        change (cut (e.symm w):ℂ)*a w=0
        rw [show cut (e.symm w)=0 from hw,Complex.ofReal_zero,zero_mul]
      simp [complexFormExteriorCoefficient,germ.fderiv_eq]
    _=(∫ z in u.target, weight (d.symm z) • complexFormExteriorCoefficient B z) := middle.symm
    _=_ := by
      symm
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero d.open_target.measurableSet (fun z hz => hz.1)
      intro z hz
      have absent : d.symm z∉tsupport weight := fun h => hz.2 ⟨hz.1,first h⟩
      have zero : weight (d.symm z)=0 := (notMem_tsupport_iff_eventuallyEq.mp absent).self_of_nhds
      rw [zero,zero_smul]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.localized_form_chart_integrals
