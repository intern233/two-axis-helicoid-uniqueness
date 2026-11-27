import TwoAxisHelicoid.ComplexCurveLocalStokes
import TwoAxisHelicoid.RectanglePoleIntegral
import Mathlib.MeasureTheory.Integral.Prod

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory Topology
open scoped Topology ComplexConjugate Interval ContDiff

/-- Lebesgue area on a closed square agrees with successive ordinary
oriented interval integrals in its real and imaginary coordinates. -/
theorem complex_square_area_eq_iterated (g : ℂ → ℂ) {r : ℝ} (hr : 0≤r)
    (hg : IntegrableOn g (Icc (-r) r ×ℂ Icc (-r) r)) :
    (∫ z in Icc (-r) r ×ℂ Icc (-r) r, g z)=
      ∫ x in -r..r, ∫ y in -r..r, g ((x:ℂ)+(y:ℂ)*I) := by
  let s := Icc (-r) r
  let e := Complex.measurableEquivRealProd.symm
  have pres : MeasurePreserving e := Complex.volume_preserving_equiv_real_prod.symm _
  have emb : MeasurableEmbedding e := e.measurableEmbedding
  have integ : IntegrableOn (fun p : ℝ × ℝ => g (e p)) (s ×ˢ s) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (pres.integrableOn_comp_preimage emb).mpr hg
  change (∫ z in s ×ℂ s, g z)=_
  rw [← pres.setIntegral_preimage_emb emb]
  change (∫ p in s ×ˢ s, g (e p))=_
  rw [Measure.volume_eq_prod,setIntegral_prod _ integ]
  have order : -r≤r := by linarith
  simp only [s,intervalIntegral.integral_of_le order,integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x _
  apply setIntegral_congr_fun measurableSet_Ioc
  intro y _
  exact congrArg g (Complex.mk_eq_add_mul_I x y)

/-- Green's formula on the actual complex square, for a C¹ complex-valued
one-form. It uses the same counterclockwise boundary as the residue integral. -/
theorem square_boundary_eq_exterior_area {a : ℂ → ℂ} {r : ℝ} (hr : 0≤r)
    (sm : ∀ z∈Icc (-r) r ×ℂ Icc (-r) r, ContDiffAt ℝ 1 a z) :
    rectangleBoundary a r r=∫ z in Icc (-r) r ×ℂ Icc (-r) r, complexFormExteriorCoefficient a z := by
  let K := Icc (-r) r ×ℂ Icc (-r) r
  have order : -r≤r := by linarith
  have cc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have diff : DifferentiableOn ℝ a K := fun z hz => ((sm z hz).differentiableAt one_ne_zero).differentiableWithinAt
  have cont : ContinuousOn (complexFormExteriorCoefficient a) K := by
    intro z hz
    have der := (sm z hz).continuousAt_fderiv one_ne_zero
    exact ((continuousAt_const.mul (der.clm_apply (continuousAt_const (y:=(1:ℂ))))).sub
      (der.clm_apply (continuousAt_const (y:=I)))).continuousWithinAt
  have integ : IntegrableOn (complexFormExteriorCoefficient a) K := cont.integrableOn_compact cc
  have domain : uIcc (-r) r ×ℂ uIcc (-r) r=K := by rw [uIcc_of_le order]
  have green := Complex.integral_boundary_rect_of_differentiableOn_real a ⟨-r,-r⟩ ⟨r,r⟩
    (domain.symm ▸ diff) (domain.symm ▸ integ)
  rw [complex_square_area_eq_iterated _ hr integ]
  simpa only [rectangleBoundary,complexFormExteriorCoefficient,smul_eq_mul,Complex.ofReal_neg,neg_mul,
    sub_eq_add_neg] using green

/-- A holomorphic one-form has zero real exterior derivative. -/
theorem complex_form_exterior_of_holomorphic {a : ℂ → ℂ} {z : ℂ}
    (h : DifferentiableAt ℂ a z) : complexFormExteriorCoefficient a z=0 := by
  have der := h.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  unfold complexFormExteriorCoefficient
  rw [der.fderiv]
  change I*(1*deriv a z)-(I*deriv a z)=0
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.square_boundary_eq_exterior_area
#print axioms TwoAxisHelicoid.complex_form_exterior_of_holomorphic
