import TwoAxisHelicoid.LocalBoundaryGraphStokes
import TwoAxisHelicoid.ComplexCurveLocalStokes
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace TwoAxisHelicoid
open Complex Set MeasureTheory Filter Topology Function
open scoped Interval ContDiff Topology

/-- The exterior coefficient of a compactly supported C¹ complex
one-form is integrable on every coordinate region. -/
theorem integrable_complex_form_exterior {f : ℂ → ℂ} (sm : ContDiff ℝ 1 f) (compact : HasCompactSupport f) :
    Integrable (complexFormExteriorCoefficient f) := by
  have integrable (v : ℂ) : Integrable (fun z => fderiv ℝ f z v) :=
    ((sm.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (compact.fderiv_apply (𝕜:=ℝ) v)
  exact ((integrable 1).const_mul I).sub (integrable I)

/-- In the plane of a complex chart the imaginary exterior coefficient
is the divergence of the pair formed from the real and negative
imaginary part of its coefficient. -/
theorem divergence_of_complex_flux {f : ℂ → ℂ} {q : ℝ×ℝ} (df : DifferentiableAt ℝ f (Complex.equivRealProdCLM.symm q)) :
    let E := Complex.equivRealProdCLM.symm
    fderiv ℝ (fun p => (f (E p)).re) q (1,0)+fderiv ℝ (fun p => -(f (E p)).im) q (0,1)=
      (complexFormExteriorCoefficient f (E q)).im := by
  let E := Complex.equivRealProdCLM.symm
  have d := df.hasFDerivAt.comp q E.hasFDerivAt
  have p : fderiv ℝ (fun y => (f (E y)).re) q=_ := (Complex.reCLM.hasFDerivAt.comp q d).fderiv
  have n : fderiv ℝ (fun y => -(f (E y)).im) q=_ := (Complex.imCLM.hasFDerivAt.comp q d).neg.fderiv
  change fderiv ℝ (fun p => (f (E p)).re) q (1,0)+fderiv ℝ (fun p => -(f (E p)).im) q (0,1)=_
  rw [p,n]
  change (fderiv ℝ f (E q) (E (1,0))).re + -(fderiv ℝ f (E q) (E (0,1))).im=_
  have x : E (1,0)=1 := by simp [E,Complex.equivRealProdCLM_symm_apply]
  have y : E (0,1)=I := by simp [E,Complex.equivRealProdCLM_symm_apply]
  rw [x,y]
  simp only [complexFormExteriorCoefficient,Complex.sub_im,Complex.mul_im,I_re,I_im,zero_mul,one_mul,zero_add]
  ring

/-- Integrate a compactly supported one-form on an arbitrary open
subset of the coordinate plane. When its support is in one regular
boundary patch, the surviving flux is the imaginary part of its
actual oriented line integral along the curved boundary. -/
theorem imaginary_form_integral_at_boundary_graph {D : Set ℂ} (op : IsOpen D)
    {φ : ℝ → ℝ} (cφ : ContDiff ℝ 2 φ) {l r d : ℝ} (lr : l≤r) (dp : 0<d)
    (side : ∀ q∈Icc (l,-d) (r,d), Complex.equivRealProdCLM.symm (realGraphShear φ q)∈D ↔ 0<q.2)
    {f : ℂ → ℂ} (sm : ContDiff ℝ 1 f) (compact : HasCompactSupport f)
    (inside : tsupport f ⊆ (Complex.equivRealProdCLM.symm ∘ realGraphShear φ) '' (Ioo l r ×ˢ Ioo (-d) d)) :
    (∫ z in D, complexFormExteriorCoefficient f z).im=
      ∫ x in l..r, ((⟨1,deriv φ x⟩:ℂ)*f (Complex.equivRealProdCLM.symm (x,φ x))).im := by
  let E := Complex.equivRealProdCLM.symm
  let Ω := E ⁻¹' D
  let P := fun q : ℝ×ℝ => (f (E q)).re
  let Q := fun q : ℝ×ℝ => -(f (E q)).im
  let K := E ⁻¹' tsupport f
  have closed : IsClosed K := (isClosed_tsupport f).preimage E.continuous
  have contained (g : ℝ×ℝ → ℝ) (off : ∀ q, f (E q)=0 → g q=0) : tsupport g⊆K := by
    apply closure_minimal _ closed
    intro q hq
    by_contra out
    exact hq (off q (image_eq_zero_of_notMem_tsupport out))
  have sub : tsupport P ∪ tsupport Q ⊆ realGraphShear φ '' (Ioo l r ×ˢ Ioo (-d) d) := by
    intro q hq
    have member : q∈K := hq.elim (fun hq => contained P (fun _ h => by simp [P,h]) hq) (fun hq => contained Q (fun _ h => by simp [Q,h]) hq)
    obtain ⟨w,hw,eq⟩ := inside member
    exact ⟨w,hw,E.injective eq⟩
  have sp : ContDiff ℝ 1 P := Complex.reCLM.contDiff.comp (sm.comp E.contDiff)
  have sq : ContDiff ℝ 1 Q := (Complex.imCLM.contDiff.comp (sm.comp E.contDiff)).neg
  have flux := open_boundary_graph_divergence cφ lr dp Ω (op.preimage E.continuous).measurableSet side sub
    (fun _ _ => sp.contDiffAt) (fun _ _ => sq.contDiffAt)
  have im := (Complex.imCLM.integral_comp_comm (φ:=complexFormExteriorCoefficient f)
    ((integrable_complex_form_exterior sm compact).integrableOn (s:=D))).symm
  have img : E '' Ω=D := E.surjective.image_preimage D
  have preserved : MeasurePreserving E volume volume := Complex.volume_preserving_equiv_real_prod.symm _
  calc
    _=∫ z in D, (complexFormExteriorCoefficient f z).im := im
    _=∫ q in Ω, (complexFormExteriorCoefficient f (E q)).im := by
      nth_rw 1 [← img]
      exact preserved.setIntegral_image_emb E.toHomeomorph.measurableEmbedding _ _
    _=∫ q in Ω, fderiv ℝ P q (1,0)+fderiv ℝ Q q (0,1) := by
      apply setIntegral_congr_fun (op.preimage E.continuous).measurableSet
      intro q _
      exact (divergence_of_complex_flux (sm.differentiable one_ne_zero (E q))).symm
    _=_ := by
      rw [flux,← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro x _
      simp only [P,Q,Complex.mul_im,one_mul]
      ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.integrable_complex_form_exterior
#print axioms TwoAxisHelicoid.imaginary_form_integral_at_boundary_graph
