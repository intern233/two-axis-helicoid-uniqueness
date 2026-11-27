import TwoAxisHelicoid.GrowingComplexRay
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology ComplexConjugate

noncomputable def exponentialPowerRay (m : ℤ) (μ : ℂ) (t : ℝ) : ℂ :=
  ((t^m:ℝ):ℂ)*exp (μ*(t:ℂ))

theorem exponentialPowerRay_norm (m : ℤ) (μ : ℂ) {t : ℝ} (pos : 0<t) :
    ‖exponentialPowerRay m μ t‖=t^m*Real.exp (μ.re*t) := by
  simp [exponentialPowerRay,norm_exp,Complex.mul_re,Real.norm_eq_abs,abs_of_pos pos]

theorem exponentialPowerRay_escape (m : ℤ) {μ : ℂ} (pos : 0<μ.re) :
    Tendsto (fun t => ‖exponentialPowerRay m μ t‖) atTop atTop := by
  apply (tendsto_exp_mul_div_rpow_atTop ((-m:ℤ):ℝ) μ.re pos).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  rw [exponentialPowerRay_norm _ _ ht,Real.rpow_intCast,zpow_neg,div_inv_eq_mul,mul_comm]

theorem exponentialPowerRay_derivatives (m : ℤ) (μ : ℂ) {t : ℝ} (pos : 0<t) :
    HasDerivAt (exponentialPowerRay m μ) (((((m:ℝ)/t:ℝ):ℂ)+μ)*exponentialPowerRay m μ t) t ∧
    HasDerivAt (fun s => ‖exponentialPowerRay m μ s‖) (((m:ℝ)/t+μ.re)*‖exponentialPowerRay m μ t‖) t := by
  have dp := hasDerivAt_zpow m t (Or.inl pos.ne')
  have p' : HasDerivAt (fun s : ℝ => s^m) ((m:ℝ)/t*t^m) t := by
    convert dp using 1
    rw [zpow_sub₀ pos.ne',zpow_one]
    ring
  have lin : HasDerivAt (fun s : ℝ => μ*(s:ℂ)) μ t := by simpa using! (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul μ
  have expD := (Complex.hasDerivAt_exp (μ*(t:ℂ))).scomp t lin
  constructor
  · have h := p'.ofReal_comp.mul expD
    change HasDerivAt (exponentialPowerRay m μ) _ t at h
    convert h using 1
    unfold exponentialPowerRay
    push_cast
    change _= _*exp (μ*(t:ℂ)) + _*(μ*exp (μ*(t:ℂ)))
    ring
  · rw [exponentialPowerRay_norm _ _ pos]
    have realD := p'.mul (((hasDerivAt_id t).const_mul μ.re).exp)
    have realD' : HasDerivAt (fun s : ℝ => s^m*Real.exp (μ.re*s)) (((m:ℝ)/t+μ.re)*(t^m*Real.exp (μ.re*t))) t := by
      change HasDerivAt (fun s : ℝ => s^m*Real.exp (μ.re*s)) _ t at realD
      convert realD using 1
      change _= (m:ℝ)/t*t^m*Real.exp (μ.re*t)+t^m*(Real.exp (μ.re*t)*(μ.re*1))
      ring
    exact realD'.congr_of_eventuallyEq ((lt_mem_nhds pos).mono fun _ hs => exponentialPowerRay_norm m μ hs)

/-- Asymptotic integration of the actual Cartesian Weierstrass
horizontal derivative on every ray with positive real exponential
growth. The inverse Gauss term is included in the derivative. -/
theorem horizontal_position_on_growing_ray (m : ℤ) {μ ζ A : ℂ}
    (positive : 0<μ.re) (na : A≠0) {g Z : ℝ → ℂ}
    (gauss : Tendsto (fun t => g t/exponentialPowerRay m μ t) atTop (𝓝 A))
    (horizontal : ∀ᶠ t in atTop, HasDerivAt Z ((conj (ζ/g t)-ζ*g t)/2) t) :
    Tendsto (fun t => Z t/exponentialPowerRay m μ t) atTop (𝓝 ((-(ζ*A)/2)/μ)) := by
  let U := exponentialPowerRay m μ
  let a := fun t : ℝ => (((m:ℝ)/t:ℝ):ℂ)+μ
  let v := fun t : ℝ => (m:ℝ)/t+μ.re
  have escape := exponentialPowerRay_escape m positive
  have invU : Tendsto (fun t => (U t)⁻¹) atTop (𝓝 0) := tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.mp escape)
  have invG : Tendsto (fun t => (g t)⁻¹) atTop (𝓝 0) := by
    have l := (gauss.inv₀ na).mul invU
    simp only [mul_zero] at l
    apply l.congr'
    filter_upwards [escape.eventually_gt_atTop 0] with t h
    change (g t/U t)⁻¹*(U t)⁻¹=(g t)⁻¹
    rw [inv_div,div_eq_mul_inv,mul_right_comm,mul_inv_cancel₀ (norm_pos_iff.mp h),one_mul]
  have tiny : Tendsto (fun t => conj (ζ/g t)/U t) atTop (𝓝 0) := by
    have l := (continuous_conj.continuousAt.tendsto.comp (invG.const_mul ζ)).mul invU
    simpa only [Function.comp_apply,mul_zero,map_zero,zero_mul,div_eq_mul_inv] using l
  have speed : Tendsto (fun t => ((conj (ζ/g t)-ζ*g t)/2)/U t) atTop (𝓝 (-(ζ*A)/2)) := by
    have l := (tiny.sub (gauss.const_mul ζ)).div_const 2
    simp only [zero_sub] at l
    exact l.congr fun t => by dsimp [U]; ring
  have realL : Tendsto (fun t : ℝ => (m:ℝ)/t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using (tendsto_const_nhds (x := (m:ℝ))).mul (tendsto_inv_atTop_zero (𝕜 := ℝ))
  apply complex_primitive_ratio_on_growing_ray (A := a) (V := v) positive escape _ _ _ speed
  · filter_upwards [horizontal,eventually_gt_atTop (0:ℝ)] with t h pos
    exact ⟨h,exponentialPowerRay_derivatives m μ pos⟩
  · simpa only [a,Function.comp_apply,ofReal_zero,zero_add] using (continuous_ofReal.continuousAt.tendsto.comp realL).add_const μ
  · simpa only [v,zero_add] using realL.add_const μ.re

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.horizontal_position_on_growing_ray
