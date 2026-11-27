import TwoAxisHelicoid.ComplexCurveLocalStokes
import TwoAxisHelicoid.ComplexEndCompactification

namespace TwoAxisHelicoid
open Complex MeasureTheory Filter Set Topology
open scoped Topology ContDiff Manifold

/-- A density computed from a complex one-form gives the same weighted
integral in two overlapping charts. The weight is an arbitrary function
on the surface, and the patch is any measurable subset of the overlap. -/
theorem complex_form_integral_on_overlap {M : Type*} [TopologicalSpace M]
    (e d : OpenPartialHomeomorph M ℂ) (a b : ℂ → ℂ)
    (weight : M → ℝ) {T : Set ℂ} (ms : MeasurableSet T) (inc : T ⊆ (e.symm.trans d).source)
    (hol : ∀ z∈(e.symm.trans d).source, AnalyticAt ℂ (e.symm.trans d) z)
    (coeff : ∀ z∈(e.symm.trans d).source, a z=b ((e.symm.trans d) z)*deriv (e.symm.trans d) z)
    (reg : ∀ z∈(e.symm.trans d).source, DifferentiableAt ℝ b ((e.symm.trans d) z)) :
    (∫ w in (e.symm.trans d) '' T, weight (d.symm w) • complexFormExteriorCoefficient b w)=
      ∫ z in T, weight (e.symm z) • complexFormExteriorCoefficient a z := by
  let u := e.symm.trans d
  have jac (x : ℂ) (hx : x∈u.source) :
      complexFormExteriorCoefficient a x= (‖deriv u x‖^2:ℝ) • complexFormExteriorCoefficient b (u x) := by
    have germ : a =ᶠ[𝓝 x] fun w => b (u w)*deriv u w :=
      Filter.mem_of_superset (u.open_source.mem_nhds hx) (fun z hz => coeff z hz)
    change I*fderiv ℝ a x 1-fderiv ℝ a x I=_
    rw [germ.fderiv_eq]
    exact complex_form_exterior_pullback (hol x hx) (reg x hx)
  change (∫ w in u '' T, weight (d.symm w) • complexFormExteriorCoefficient b w)=_
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume ms
    (fun z hz => ((hol z (inc hz)).differentiableAt.restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt)
    (u.injOn.mono inc)]
  apply setIntegral_congr_fun ms
  intro z hz
  have inD : e.symm z∈d.source := (show z∈(e.symm.trans d).source from inc hz).2
  have same : d.symm (u z)=e.symm z := d.left_inv inD
  change |(fderiv ℝ u z).det| • (weight (d.symm (u z)) • complexFormExteriorCoefficient b (u z))=weight (e.symm z) • complexFormExteriorCoefficient a z
  rw [show (fderiv ℝ u z).det=‖deriv u z‖^2 from holomorphic_real_jacobian (hol z (inc hz)).differentiableAt,abs_of_nonneg (sq_nonneg _),
    same,jac z (inc hz),smul_comm]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.complex_form_integral_on_overlap
