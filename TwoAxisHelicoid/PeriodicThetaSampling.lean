import TwoAxisHelicoid.PeriodicRootQuadrature
import TwoAxisHelicoid.AllHorizontalRegularity
import TwoAxisHelicoid.RhombicPrimitivePatches

namespace TwoAxisHelicoid
open Complex MeasureTheory Set
open scoped ComplexConjugate
attribute [local irreducible] thetaA

/-- Reflection of the analytic midline kernel across its real parameter axis,
followed by translation through one real half-period. -/
private theorem midline_complex_half {t : ℝ} (ht : 0<t) (a : ℝ) (z : ℂ) :
    thetaA t a (z+1+I*((t/2:ℝ):ℂ)) =
      conj (thetaA t a (conj z+I*((t/2:ℝ):ℂ))) := by
  have eq : z+1+I*((t/2:ℝ):ℂ)=conj (conj z+I*((t/2:ℝ):ℂ))+(1+I*t) := by
    simp only [map_add,map_mul,Complex.conj_conj,Complex.conj_I,Complex.conj_ofReal]
    push_cast
    ring
  rw [eq,thetaA_complex_period ht a,thetaA_conj]

/-- The symmetrized complex integrand is unit-periodic and agrees on the
real axis with the real part used for the manuscript's horizontal period. -/
theorem periodic_theta_sample_error {t a s M : ℝ} {N : ℕ} (hn : 0<N) (positive : 0<s) (width : 2*s<t)
    (bound : ∀ z : ℂ, z.re∈Icc (-1:ℝ) 0 → |z.im|=s →
      ‖thetaA t a (z+I*((t/2:ℝ):ℂ))‖≤M) :
    let r := Real.exp (-(2*Real.pi*((N:ℝ)*s)))
    |(1/(N:ℝ))*(∑ k∈Finset.range N,
      (thetaA t a (((-1+(k:ℝ)/N:ℝ):ℂ)+I*((t/2:ℝ):ℂ))).re)-thetaHorizontalPeriod t a|
      ≤2*(M*r/(1-r)) := by
  have ht0 : 0<t := by linarith
  let F := fun z : ℂ => thetaA t a (z+I*((t/2:ℝ):ℂ))
  let J := fun z : ℂ => (F (z-1)+F z)/2
  have per : Function.Periodic J 1 := by
    intro z
    have h : F (z+1)=F (z-1) := by
      exact (show F (z+1)=thetaA t a ((z-1+I*((t/2:ℝ):ℂ))+2) by
        change thetaA t a _=thetaA t a _;congr 1;ring).trans (thetaA_periodic t a _)
    simp only [J,add_sub_cancel_right,h,add_comm (F z)]
  have realJ (x : ℝ) : J (x:ℂ)=((F (((x-1:ℝ):ℂ))).re:ℂ) := by
    have hc := thetaA_midline_add_one ht0 a (x-1)
    rw [sub_add_cancel] at hc
    change F (x:ℂ)=conj (F (((x-1:ℝ):ℂ))) at hc
    simp only [J,← Complex.ofReal_one,← Complex.ofReal_sub,hc,Complex.add_conj]
    push_cast
    ring
  have holF (z : ℂ) (zi : |z.im|≤s) : DifferentiableAt ℂ F z := by
    have nz := (thetaJet_zero_iff_rhombic_lattice_of_pos ht0 (z+I*((t/2:ℝ):ℂ))).not.mpr
      (rhombic_horizontal_strip_not_mem ht0 (by
        change 0<(z+I*((t/2:ℝ):ℂ)).im ∧ (z+I*((t/2:ℝ):ℂ)).im<t
        simp only [Complex.add_im,Complex.mul_im,Complex.I_re,Complex.I_im,
          Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add]
        constructor <;> linarith [(abs_le.mp zi).1,(abs_le.mp zi).2]))
    exact (thetaA_differentiableAt ht0 a nz).comp z (differentiableAt_id.add_const _)
  have hol (z : ℂ) (zi : |z.im|≤s) : DifferentiableAt ℂ J z := by
    exact (((holF (z-1) (by simpa only [Complex.sub_im,Complex.one_im,sub_zero] using zi)).comp z
      (differentiableAt_id.sub_const 1)).add (holF z zi)).div_const 2
  have bd (z : ℂ) (zi : |z.im|=s) : ‖J z‖≤M := by
    let n : ℤ := ⌊z.re⌋
    let w := z-(n:ℂ)
    have xr : (w-1).re∈Icc (-1:ℝ) 0 := by
      simp only [w,Complex.sub_re,Complex.intCast_re,Complex.one_re,mem_Icc]
      change -1≤Int.fract z.re-1 ∧ Int.fract z.re-1≤0
      constructor <;> linarith only [Int.fract_nonneg z.re,Int.fract_lt_one z.re]
    have yi : |(w-1).im|=s := by
      simpa only [w,Complex.sub_im,Complex.one_im,Complex.intCast_im,sub_zero] using zi
    have e : J z=J w := by
      have h := per.int_mul n w
      simpa only [w,mul_one,sub_add_cancel] using h
    have fw : F w=conj (F (conj (w-1))) := by
      simpa only [sub_add_cancel,F] using midline_complex_half ht0 a (w-1)
    have b₁ := bound _ xr yi
    have b₂ := bound (conj (w-1)) (by simpa only [Complex.conj_re] using xr)
      (by simpa only [Complex.conj_im,abs_neg] using yi)
    change ‖F (w-1)‖≤_ at b₁
    change ‖F (conj (w-1))‖≤_ at b₂
    rw [e]
    change ‖(F (w-1)+F w)/2‖≤_
    rw [norm_div,Complex.norm_ofNat,div_le_iff₀ (by norm_num : (0:ℝ)<2)]
    have b₃ : ‖F w‖≤M := by rw [fw,Complex.norm_conj];exact b₂
    linarith [norm_add_le (F (w-1)) (F w)]
  have integral : (∫ x : ℝ in 0..1,J (x:ℂ))=(thetaHorizontalPeriod t a:ℂ) := by
    let g := fun x : ℝ => (F (x:ℂ)).re
    have c : Continuous g := Complex.continuous_re.comp (horizontal_integrand_continuous ht0 a)
    simp_rw [realJ]
    change (∫ x : ℝ in 0..1,((g (x-1)):ℂ))=_
    rw [intervalIntegral.integral_comp_sub_right (fun x => (g x:ℂ))]
    norm_num only [zero_sub,one_ne_zero,sub_self]
    rw [intervalIntegral.integral_ofReal,horizontal_period_half ht0 a]
    congr 1
    exact Complex.reCLM.intervalIntegral_comp_comm ((horizontal_integrand_continuous ht0 a).intervalIntegrable (-1) 0 (μ:=volume))
  have sample : periodicSampleAverage N J 0=
      (((1/(N:ℝ))*(∑ k∈Finset.range N,(F (((-1+(k:ℝ)/N:ℝ):ℂ))).re):ℝ):ℂ) := by
    unfold periodicSampleAverage
    push_cast
    simp only [one_div]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    have h := realJ ((k:ℝ)/N)
    push_cast at h
    simpa [sub_eq_add_neg, add_comm] using h
  have quad := periodic_strip_trapezoidal_error hn per positive hol bd
  rw [integral,sample,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at quad
  exact quad


end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.periodic_theta_sample_error
