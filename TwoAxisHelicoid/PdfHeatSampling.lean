import TwoAxisHelicoid.PdfHeatPathDerivative
import TwoAxisHelicoid.PeriodicRootQuadrature
import TwoAxisHelicoid.RhombicPrimitivePatches
import Mathlib.Analysis.Complex.ExponentialBounds

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
attribute [local irreducible] thetaA thetaQuotient thetaJet

private theorem heat_periodic (t a d : ℝ) : Function.Periodic (pdfHeatKernel t a d) 2 := by
  intro z
  have hm : (Real.pi*(z+2-a)/2:ℂ)=Real.pi*(z-a)/2+Real.pi := by ring
  have h : (Real.pi*(z+2)/2:ℂ)=Real.pi*z/2+Real.pi := by ring
  simp only [pdfHeatKernel,thetaA_periodic t a z,thetaLt,thetaLa,hm,h,thetaQuotient_add_pi]

private theorem heat_holomorphic {t : ℝ} (ht : 0<t) (a d : ℝ) {z : ℂ} (hz : z∈complexHorizontalStrip 0 t) :
    DifferentiableAt ℂ (pdfHeatKernel t a d) z := by
  have regular {w : ℂ} (hw : w∈complexHorizontalStrip 0 t) : w∈thetaRegular t :=
    (thetaJet_zero_iff_rhombic_lattice_of_pos ht w).not.mpr (rhombic_horizontal_strip_not_mem ht hw)
  have rg := regular hz
  have rm : z-(a:ℂ)∈thetaRegular t := regular (by
    change 0<(z-(a:ℂ)).im ∧ (z-(a:ℂ)).im<t
    simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using (show 0<z.im ∧ z.im<t from hz))
  have D (j : ℕ) : DifferentiableAt ℂ (fun w : ℂ => thetaQuotient t j (Real.pi*w/2)) z :=
    (thetaQuotient_hasDerivAt ht j _ rg).differentiableAt.comp z
      (f := fun w : ℂ => Real.pi*w/2) (by fun_prop)
  have E (j : ℕ) : DifferentiableAt ℂ (fun w : ℂ => thetaQuotient t j (Real.pi*(w-a)/2)) z :=
    (thetaQuotient_hasDerivAt ht j _ rm).differentiableAt.comp z
      (f := fun w : ℂ => Real.pi*(w-a)/2) (by fun_prop)
  have lt : DifferentiableAt ℂ (thetaLt t a) z :=
    (((differentiableAt_const _).add (E 2) |>.sub (D 2)).const_mul _).add
      (((D 3).sub ((D 1).mul (D 2))).const_mul _)
  have la : DifferentiableAt ℂ (thetaLa t a) z := (((D 1).sub (E 1)).sub_const _).const_mul _
  exact (thetaA_differentiableAt ht a rg).mul (lt.add (la.const_mul _))

/-- A contour enclosure for the exact heat integrand bounds the difference
between its sampled real mean and its full two-unit period. -/
theorem pdf_heat_sampling {t a d s M : ℝ} {N : ℕ} (hn : 0<N) (hs : 0<s) (width : 2*s<t)
    (bound : ∀ z : ℂ, z.re∈Icc (-1:ℝ) 1 → |z.im|=s →
      ‖pdfHeatKernel t a d (z+I*((t/2:ℝ):ℂ))‖≤M) :
    let r := Real.exp (-(2*Real.pi*((N:ℝ)*(s/2))))
    |(1/(N:ℝ))*(∑ k∈Finset.range N,
      (pdfHeatKernel t a d (((2*((k:ℝ)/N)-1:ℝ):ℂ)+I*((t/2:ℝ):ℂ))).re)-
      (1/2:ℝ)*(∫ x : ℝ in (-1)..1,pdfHeatKernel t a d ((x:ℂ)+I*((t/2:ℝ):ℂ))).re|≤2*(M*r/(1-r)) := by
  let K := pdfHeatKernel t a d
  let F := fun z : ℂ => K (2*z-1+I*((t/2:ℝ):ℂ))
  have per : Function.Periodic F 1 := by
    intro z
    exact (show F (z+1)=K ((2*z-1+I*((t/2:ℝ):ℂ))+2) by dsimp only [F];congr 1;ring).trans
      (heat_periodic t a d _)
  have im (z : ℂ) : (2*z-1+I*((t/2:ℝ):ℂ)).im=2*z.im+t/2 := by
    simp
  have hol (z : ℂ) (hz : |z.im|≤s/2) : DifferentiableAt ℂ F z := by
    apply (heat_holomorphic (by linarith : 0<t) a d ?_).comp z
      (f:=fun w : ℂ => 2*w-1+I*((t/2:ℝ):ℂ)) (by fun_prop)
    change 0<(2*z-1+I*((t/2:ℝ):ℂ)).im ∧ (2*z-1+I*((t/2:ℝ):ℂ)).im<t
    rw [im]
    constructor <;> linarith [(abs_le.mp hz).1,(abs_le.mp hz).2]
  have bd (z : ℂ) (iz : |z.im|=s/2) : ‖F z‖≤M := by
    let n : ℤ := ⌊z.re⌋
    let w := z-(n:ℂ)
    have xr : 0≤w.re ∧ w.re≤1 := by
      simp only [w,Complex.sub_re,Complex.intCast_re]
      change 0≤Int.fract z.re ∧ Int.fract z.re≤1
      exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    have edge : |(2*w-1).im|=s := by
      have eq : (2*w-1).im=2*z.im := by simp [w, two_mul]
      rw [eq, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2), iz]
      ring
    have e : F z=F w := by simpa only [w,mul_one,sub_add_cancel] using per.int_mul n w
    rw [e]
    have eq : (2*w-1).re=2*w.re-1 := by simp [two_mul]
    exact bound _ (by rw [eq]; constructor <;> linarith [xr.1,xr.2]) edge
  have core := periodic_strip_trapezoidal_error hn per (by linarith : 0<s/2) hol bd
  let g := fun x : ℝ => K ((x:ℂ)+I*((t/2:ℝ):ℂ))
  have it : (∫ x : ℝ in 0..1,F (x:ℂ))=(2:ℝ)⁻¹ • ∫ x : ℝ in (-1)..1,g x := by
    have e (x : ℝ) : F (x:ℂ)=g (2*x-1) := by simp only [F,g,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_one]
    simp_rw [e]
    change (∫ x : ℝ in 0..1,(fun u : ℝ => g (u-1)) (2*x))=_
    have scale := intervalIntegral.integral_comp_mul_left (fun u : ℝ => g (u-1)) (a:=0) (b:=1) (by norm_num : (2:ℝ)≠0)
    have shift := intervalIntegral.integral_comp_sub_right (a:=(0:ℝ)) (b:=2) g 1
    norm_num at scale shift ⊢
  have reSample : (periodicSampleAverage N F 0).re =
      (1/(N:ℝ))*∑ k∈Finset.range N,(K (((2*((k:ℝ)/N)-1:ℝ):ℂ)+I*((t/2:ℝ):ℂ))).re := by
    have scalar (r : ℝ) (u : ℂ) : ((r:ℂ)*u).re = r*u.re := by simp [Complex.mul_re]
    unfold periodicSampleAverage
    rw [show (N:ℂ)⁻¹=(((N:ℝ)⁻¹:ℝ):ℂ) by push_cast; rfl, scalar, Complex.re_sum]
    simp [F,one_div]
  have q := (Complex.abs_re_le_norm _).trans core
  rw [Complex.sub_re,reSample,it,Complex.real_smul] at q
  simpa [Complex.mul_re,one_div,g,K] using q

theorem pdf_heat_32_point_period_error {t a d : ℝ} (lower : 17/20≤t)
    (bd : ∀ z : ℂ, z.re∈Icc (-1:ℝ) 1 → |z.im|=3/16 →
      ‖pdfHeatKernel t a d
        (z+I*((t/2:ℝ):ℂ))‖≤10^7) :
    |(1/32:ℝ)*(∑ k∈Finset.range 32,
      (pdfHeatKernel t a d
        (((2*((k:ℝ)/32)-1:ℝ):ℂ)+I*((t/2:ℝ):ℂ))).re)-(1/2:ℝ)*(∫ x : ℝ in (-1)..1, pdfHeatKernel t a d ((x:ℂ)+I*((t/2:ℝ):ℂ))).re|≤1/5 := by
  have s := pdf_heat_sampling (N:=32) (by decide) (s:=3/16) (by norm_num) (by linarith) bd
  apply s.trans
  let r := Real.exp (-(2*Real.pi*((32:ℝ)*(3/16/2))))
  have exp18 : (27/10:ℝ)^18≤Real.exp 18 := by
    rw [show (18:ℝ)=(18:ℕ)*(1:ℝ) by norm_num,Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
  have ex : (27/10:ℝ)^18*(1+4/5)≤Real.exp (18+4/5) := by
    rw [Real.exp_add]
    exact mul_le_mul exp18 (by linarith [Real.add_one_le_exp (4/5:ℝ)]) (by norm_num) (Real.exp_pos _).le
  have upper : r≤1/100000010 := by
    dsimp only [r]
    simp only [Real.exp_neg,one_div]
    apply inv_anti₀ (by norm_num)
    exact ((by norm_num : (100000010:ℝ)≤(27/10)^18*(1+4/5)).trans ex).trans
      (Real.exp_le_exp.mpr (by linarith [Real.pi_gt_d2]))
  change 2*((10:ℝ)^7*r/(1-r))≤_
  have pos : 0<1-r := by linarith
  rw [← mul_div_assoc,div_le_iff₀ pos]
  linarith

theorem original_pdf_heat_32_point_error {t : ℝ} (ht : t∈Ioo (0:ℝ) ellipticVerticalUpper) (lower : 17/20≤t)
    (bd : ∀ z : ℂ, z.re∈Icc (-1:ℝ) 1 → |z.im|=3/16 →
      ‖pdfHeatKernel t (verticalA t) (-(thetaGt t (verticalA t)).re/(thetaGa t (verticalA t)).re)
        (z+I*((t/2:ℝ):ℂ))‖≤10^7) :
    |(1/32:ℝ)*(∑ k∈Finset.range 32,
      (pdfHeatKernel t (verticalA t) (-(thetaGt t (verticalA t)).re/(thetaGa t (verticalA t)).re)
        (((2*((k:ℝ)/32)-1:ℝ):ℂ)+I*((t/2:ℝ):ℂ))).re)-deriv actualPeriodAlong t|≤1/5 := by
  rw [original_pdf_heat_derivative_formula ht]
  exact pdf_heat_32_point_period_error lower bd

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.pdf_heat_sampling
#print axioms TwoAxisHelicoid.original_pdf_heat_32_point_error
