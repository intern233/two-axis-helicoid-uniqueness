import TwoAxisHelicoid.FullPeriodBranch
import TwoAxisHelicoid.EllipticPeriodDerivative
import TwoAxisHelicoid.ThetaDerivativeHolomorphic
import TwoAxisHelicoid.HorizontalPeriodCentered

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology
attribute [local irreducible] thetaA thetaJet thetaAa thetaAtMidline thetaLt thetaLa thetaQuotient

noncomputable def pdfHeatKernel (t a d : ℝ) (z : ℂ) : ℂ :=
  thetaA t a z*(thetaLt t a z+(d:ℂ)*thetaLa t a z)

private theorem heat_moving_real_period {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 2) (d : ℝ) :
    Function.Periodic (fun x : ℝ =>
      (thetaAtMidline t a ((x:ℂ)+I*((t/2:ℝ):ℂ))+
        (d:ℂ)*thetaAa t a ((x:ℂ)+I*((t/2:ℝ):ℂ))).re) 1 := by
  let b := fun s : ℝ => a+(s-t)*d
  let h := fun (x s : ℝ) => (thetaA s (b s) ((x:ℂ)+I*((s/2:ℝ):ℂ))).re
  let u := fun x : ℝ =>
    (thetaAtMidline t a ((x:ℂ)+I*((t/2:ℝ):ℂ))+(d:ℂ)*thetaAa t a ((x:ℂ)+I*((t/2:ℝ):ℂ))).re
  have atT : b t=a := by simp [b]
  have db : HasDerivAt b d t := by
    simpa only [b,id_eq,one_mul] using (((hasDerivAt_id t).sub_const t).mul_const d).const_add a
  have each (x : ℝ) : HasDerivAt (h x) (u x) t := by
    have arg : HasDerivAt (fun s : ℝ => (x:ℂ)+I*((s/2:ℝ):ℂ)) (I/2) t := by
      convert (((hasDerivAt_id t).div_const 2).ofReal_comp.const_mul I).const_add (x:ℂ) using 1 <;> simp [div_eq_mul_inv]
    have curve := thetaA_curve_hasDerivAt (hasDerivAt_id t) db arg ht (thetaJet_one_at_zero_ne_zero_of_pos ht)
      (by rw [atT];exact theta_vertical_denominator ht ha.1 ha.2) (horizontal_midline_regular ht x)
      (by rw [atT];exact horizontal_shift_regular ht a x)
    have dreal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t curve
    change HasDerivAt (h x) _ t at dreal
    convert dreal using 1
    change (thetaAtMidline t a _+(d:ℂ)*thetaAa t a _).re=(_ : ℂ).re
    congr 1
    simp only [atT,id_eq,thetaAtMidline,thetaAa,Complex.ofReal_one,one_mul]
    ring
  intro x
  have eq : h (x+1)=ᶠ[𝓝 t] h x := by
    filter_upwards [lt_mem_nhds ht] with s hs
    exact horizontal_real_integrand_period_one hs (b s) x
  exact (each (x+1)).unique ((each x).congr_of_eventuallyEq eq)

theorem pdf_heat_full_integral {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 2) (d : ℝ) :
    horizontalPeriodDt t a+d*horizontalPeriodDa t a=
      (1/2:ℝ)*(∫ x : ℝ in (-1)..1, pdfHeatKernel t a d ((x:ℂ)+I*((t/2:ℝ):ℂ))).re := by
  let z := fun x : ℝ => (x:ℂ)+I*((t/2:ℝ):ℂ)
  let f := fun x : ℝ => thetaAtMidline t a (z x)
  let g := fun x : ℝ => thetaAa t a (z x)
  let w := fun x : ℝ => deriv (thetaA t a) (z x)
  let total := fun x : ℝ => f x+(d:ℂ)*g x
  have zc : Continuous z := Complex.continuous_ofReal.add_const _
  have cf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have outer : ContinuousAt (thetaAtMidline t a) (z x) := (thetaAtMidline_differentiableAt ht a
      (horizontal_midline_regular ht x) (horizontal_shift_regular ht a x)).continuousAt
    exact outer.comp (show ContinuousAt z x from zc.continuousAt)
  have cg : Continuous g := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have outer : ContinuousAt (thetaAa t a) (z x) := (thetaAa_differentiableAt ht a
      (horizontal_midline_regular ht x) (horizontal_shift_regular ht a x)).continuousAt
    exact outer.comp (show ContinuousAt z x from zc.continuousAt)
  have cw : Continuous w := (thetaA_deriv_continuousOn ht a).comp_continuous zc
    (fun x => horizontal_midline_regular ht x)
  have ct : Continuous total := cf.add (continuous_const.mul cg)
  have half : horizontalPeriodDt t a+d*horizontalPeriodDa t a=(∫ x : ℝ in (-1)..0,total x).re := by
    unfold horizontalPeriodDt horizontalPeriodDa
    rw [show (∫ x : ℝ in (-1)..0,total x)=(∫ x : ℝ in (-1)..0,f x)+(d:ℂ)*(∫ x : ℝ in (-1)..0,g x) by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_add (cf.intervalIntegrable _ _)
        ((continuous_const.mul cg).intervalIntegrable _ _)]
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,f,g,z]
  have realpart (l u : ℝ) : (∫ x in l..u,total x).re=∫ x in l..u,(total x).re :=
    (Complex.reCLM.intervalIntegral_comp_comm (ct.intervalIntegrable l u (μ:=volume))).symm
  have per := (heat_moving_real_period ht ha d).intervalIntegral_add_eq (-1) 0
  change (∫ x : ℝ in (-1)..(-1)+1,(total x).re)=(∫ x : ℝ in 0..0+1,(total x).re) at per
  norm_num only [neg_add_cancel,zero_add] at per
  have adj := intervalIntegral.integral_add_adjacent_intervals
    ((Complex.continuous_re.comp ct).intervalIntegrable (-1) 0 (μ:=volume))
    ((Complex.continuous_re.comp ct).intervalIntegrable 0 1 (μ:=volume))
  change (∫ x : ℝ in (-1)..0,(total x).re)+(∫ x : ℝ in 0..1,(total x).re)=
    ∫ x : ℝ in (-1)..1,(total x).re at adj
  have full : horizontalPeriodDt t a+d*horizontalPeriodDa t a=(1/2:ℝ)*(∫ x : ℝ in (-1)..1,total x).re := by
    rw [half,realpart,realpart]
    linarith
  have split (x : ℝ) : pdfHeatKernel t a d (z x)=total x-(I/2)*w x := by
    have dA := thetaA_spatial_deriv ht a (theta_vertical_denominator ht ha.1 ha.2)
      (horizontal_midline_regular ht x) (horizontal_shift_regular ht a x)
    change thetaA t a (z x)*(thetaLt t a (z x)+(d:ℂ)*thetaLa t a (z x))=_
    dsimp only [total,w,f,g]
    rw [show deriv (thetaA t a) (z x)=thetaA t a (z x)*thetaLz t a (z x) from dA]
    unfold thetaAtMidline thetaAa
    ring
  have dw : (∫ x : ℝ in (-1)..1,w x)=0 :=
    thetaA_integral_spatial_derivative_zero ht a (t/2) (fun x _ => horizontal_midline_regular ht x)
  rw [full]
  change _=(1/2:ℝ)*(∫ x : ℝ in (-1)..1,pdfHeatKernel t a d (z x)).re
  simp_rw [split]
  have iw : IntervalIntegrable (fun x => (I/2)*w x) volume (-1) 1 := (continuous_const.mul cw).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (ct.intervalIntegrable _ _) iw,
    intervalIntegral.integral_const_mul,dw,mul_zero,sub_zero]

/-- The full period, the derivative along the actual vertical branch, and
the integrand used by the attached heat certificate agree exactly. -/
theorem original_pdf_heat_derivative_formula {t : ℝ} (ht : t∈Ioo (0:ℝ) ellipticVerticalUpper) :
    deriv actualPeriodAlong t=(1/2:ℝ)*(∫ x : ℝ in (-1)..1,
      pdfHeatKernel t (verticalA t) (-(thetaGt t (verticalA t)).re/(thetaGa t (verticalA t)).re)
        ((x:ℂ)+I*((t/2:ℝ):ℂ))).re := by
  have ha := (verticalA_spec ht).1
  rw [(actualPeriodAlong_hasDerivAt ht).deriv,pdf_heat_full_integral ht.1 ⟨ha.1,ha.2.trans (by norm_num)⟩,
    (verticalA_hasDerivAt ht).deriv]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.pdf_heat_full_integral
#print axioms TwoAxisHelicoid.original_pdf_heat_derivative_formula
