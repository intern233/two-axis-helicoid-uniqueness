import TwoAxisHelicoid.JacobiChordKernel
import TwoAxisHelicoid.ComplexBallChecked
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid
open Set Complex MeasureTheory
open scoped ComplexConjugate
attribute [local irreducible] thetaA dualThetaA jacobiChordKernel

noncomputable def pdfPrimalHorizontalIntegral (t a : ℝ) : ℂ :=
  (∫ x : ℝ in (-1)..1, thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ)))/2

noncomputable def pdfDualHorizontalIntegral (t a : ℝ) : ℂ :=
  ∫ x : ℝ in (-1/2)..(1/2), dualThetaA t a ((1/2:ℂ)+I*((x/t:ℝ):ℂ))

/-- The full original theta path used by the negative JSON table is
exactly real. In the positive table, the shorter dual path retains its
imaginary part. -/
theorem pdf_primal_horizontal_integral_real {t : ℝ} (ht : 0<t) (a : ℝ) :
    pdfPrimalHorizontalIntegral t a=(thetaHorizontalPeriod t a:ℂ) := by
  have hc := horizontal_integrand_continuous ht a
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-1) 0 (μ:=volume)) (hc.intervalIntegrable 0 1 (μ:=volume))
  rw [pdfPrimalHorizontalIntegral,← hs,horizontal_integral_halves ht a,horizontal_period_half ht a]
  have h (w : ℂ) : (w+conj w)/2=(w.re:ℂ) := by rw [Complex.add_conj];push_cast;ring
  exact h _

theorem pdf_dual_horizontal_integral_chord {t a : ℝ} (ht : 0<t) (htmax : t≤7/5)
    (ha : 0<a) (hb : a<1) :
    pdfDualHorizontalIntegral t a=∫ s : ℝ in (-1)..1, jacobiChordKernel t a (s:ℂ) := by
  let H := leftChordH (leftNome t)
  let K := leftChordK (leftNome t)
  have nome := (leftNome_lt_one_third ht htmax).le
  obtain ⟨g,hg⟩ := jacobiChordDifferential_exact_ball ht nome a
  have arc := jacobiArc_primitive_difference ht ha hb hg
  have line := jacobiChord_line_primitive_difference ht nome a hg
  have hsub := intervalIntegral.integral_comp_div
    (fun y : ℝ => dualThetaA t a (leftPathW y)) ht.ne' (a:=(-1/2:ℝ)) (b:=(1/2:ℝ))
  simp only [div_div,neg_div,Complex.real_smul] at hsub
  have toArc : pdfDualHorizontalIntegral t a=
      -(∫ y : ℝ in (-(1/(2*t)))..(1/(2*t)),jacobiArcDifferential t a y) := by
    have eval (y : ℝ) : jacobiArcDifferential t a y= -(t:ℂ)*dualThetaA t a (leftPathW y) := by
      unfold jacobiArcDifferential
      simp only [← mul_assoc]
      rw [← pow_two,I_sq,neg_one_mul]
    unfold pdfDualHorizontalIntegral
    change (∫ x : ℝ in (-1/2)..(1/2),dualThetaA t a (leftPathW (x/t)))=_
    simp only [neg_div]
    rw [hsub]
    simp_rw [eval]
    rw [intervalIntegral.integral_const_mul,neg_mul,neg_neg]
  have scaled := intervalIntegral.smul_integral_comp_mul_left
    (fun v : ℝ => I*jacobiChordDifferential t a ((H:ℂ)+I*(v:ℂ))) K (a:=-1) (b:=1)
  simp only [mul_neg_one,mul_one,Complex.real_smul] at scaled
  rw [toArc,arc,neg_sub,← line]
  change (∫ v : ℝ in (-K)..K,I*jacobiChordDifferential t a ((H:ℂ)+I*(v:ℂ)))=_
  rw [← scaled,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  unfold jacobiChordKernel jacobiChordPoint
  dsimp only [H,K]
  push_cast
  ring

theorem pdf_horizontal_imag_bounds {z : ℂ} {b : ComplexBall} (inside : b.Contains z) :
    ((b.center.im-b.radius:ℚ):ℝ)≤z.im ∧ z.im≤((b.center.im+b.radius:ℚ):ℝ) := by
  have h := (Complex.abs_im_le_norm (z-b.center.val)).trans inside
  rw [Complex.sub_im] at h
  have l := (abs_le.mp h).1
  have u := (abs_le.mp h).2
  change -(b.radius:ℝ)≤z.im-(b.center.im:ℝ) at l
  change z.im-(b.center.im:ℝ)≤(b.radius:ℝ) at u
  push_cast
  exact ⟨by linarith,by linarith⟩

/-- All 59 recorded imaginary intervals for the original full-period
path include the actual integral, for every a on each parameter box. -/
theorem negative_table_actual_imaginary_intervals :
    ∀ r∈CertificateData.negativeData, ∀ t a : ℝ, CertificateSemantics.RealMem r.t t →
      CertificateSemantics.RealMem r.hImag (pdfPrimalHorizontalIntegral t a).im := by
  have arithmetic : CertificateData.negativeData.all (fun r => decide
      (0<r.t.lower ∧ r.hImag.lower≤0 ∧ 0≤r.hImag.upper))=true := by decide +kernel
  intro r hr t a ht
  obtain ⟨pos,lo,hi⟩ := of_decide_eq_true (List.all_eq_true.mp arithmetic r hr)
  have htp := ((Rat.cast_pos (K:=ℝ)).mpr pos).trans_le ht.1
  rw [pdf_primal_horizontal_integral_real htp,Complex.ofReal_im]
  exact ⟨by exact_mod_cast lo,by exact_mod_cast hi⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.pdf_dual_horizontal_integral_chord
#print axioms TwoAxisHelicoid.negative_table_actual_imaginary_intervals
