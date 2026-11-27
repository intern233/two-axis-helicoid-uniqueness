import TwoAxisHelicoid.UnivalentImageDirichletEnergy
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

namespace TwoAxisHelicoid
open Complex Set MeasureTheory Filter Topology
open scoped Topology ContDiff

/-- Coefficient of the exterior derivative of the complex one-form
a(z) dz relative to the oriented real area dx dy. -/
noncomputable def complexFormExteriorCoefficient (a : ℂ → ℂ) (z : ℂ) : ℂ :=
  I * fderiv ℝ a z 1 - fderiv ℝ a z I

private theorem directional_integral_zero {a : ℂ → ℂ} (sm : ContDiff ℝ 1 a)
    (compact : HasCompactSupport a) (v : ℂ) : (∫ z, fderiv ℝ a z v)=0 := by
  have dc : Continuous (fun z => fderiv ℝ a z v) := (sm.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have der : Integrable (fun z => fderiv ℝ a z v) volume := dc.integrable_of_hasCompactSupport (compact.fderiv_apply (𝕜:=ℝ) v)
  have func : Integrable a volume := sm.continuous.integrable_of_hasCompactSupport compact
  have byParts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ:=volume) (f:=fun _ : ℂ => (1:ℂ)) (g:=a) (v:=v)
    (by simp) (by simpa only [one_mul] using der) (by simpa only [one_mul] using func)
    (fun _ _ => differentiableAt_const _) (fun z _ => sm.differentiable one_ne_zero z)
  simpa using byParts

/-- Stokes in a complex chart for an arbitrary compactly supported C¹
coefficient. No integrability or rectangular support bound is an input. -/
theorem compact_complex_form_stokes {a : ℂ → ℂ} (sm : ContDiff ℝ 1 a) (compact : HasCompactSupport a) :
    (∫ z, complexFormExteriorCoefficient a z)=0 := by
  have integ (v : ℂ) : Integrable (fun z => fderiv ℝ a z v) := by
    have c : Continuous (fun z => fderiv ℝ a z v) := (sm.continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact c.integrable_of_hasCompactSupport (compact.fderiv_apply (𝕜:=ℝ) v)
  change (∫ z, I*fderiv ℝ a z 1-fderiv ℝ a z I)=0
  rw [integral_sub ((integ 1).const_mul _) (integ I),integral_const_mul,
    directional_integral_zero sm compact 1,directional_integral_zero sm compact I,mul_zero,sub_zero]

private theorem complex_linear_change_area_factor (T : ℂ →L[ℝ] ℂ) (d : ℂ) :
    d*(I*T d-T (I*d))=(‖d‖^2:ℝ) • (I*T 1-T I) := by
  have expand (w : ℂ) : T w=w.re • T 1+w.im • T I := by
    have eq : w=w.re • (1:ℂ)+w.im • I := by simpa only [Complex.real_smul,mul_one] using w.re_add_im.symm
    calc T w=T (w.re • (1:ℂ)+w.im • I) := congrArg T eq
         _=_ := by simp only [map_add,map_smul]
  rw [expand d,expand (I*d),← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,
    Complex.real_smul] <;> ring

/-- Under a holomorphic change of chart the exterior coefficient of a
pulled-back one-form transforms by the positive real area Jacobian. -/
theorem complex_form_exterior_pullback {a u : ℂ → ℂ} {z : ℂ}
    (du : AnalyticAt ℂ u z) (da : DifferentiableAt ℝ a (u z)) :
    complexFormExteriorCoefficient (fun w => a (u w)*deriv u w) z =
      (‖deriv u z‖^2:ℝ) • complexFormExteriorCoefficient a (u z) := by
  let T := fderiv ℝ a (u z)
  let d := deriv u z
  let k := deriv (deriv u) z
  have du' := du.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have dk := du.deriv.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have df := (da.hasFDerivAt.comp z du').mul dk
  unfold complexFormExteriorCoefficient
  have derivative : fderiv ℝ (fun w => a (u w)*deriv u w) z=_ := df.fderiv
  rw [derivative]
  change I*(a (u z)*(1*k)+d*T (1*d))-(a (u z)*(I*k)+d*T (I*d))=_
  simp only [one_mul]
  calc I*(a (u z)*k+d*T d)-(a (u z)*(I*k)+d*T (I*d))=d*(I*T d-T (I*d)) := by ring
       _=_ := complex_linear_change_area_factor T d

/-- The integral of the exterior coefficient agrees on both sides of
an injective holomorphic chart change over any measurable patch. -/
theorem complex_form_exterior_integral_pullback {a u : ℂ → ℂ} {S : Set ℂ}
    (ms : MeasurableSet S) (one : InjOn u S) (hol : ∀ z∈S, AnalyticAt ℂ u z)
    (diff : ∀ z∈S, DifferentiableAt ℝ a (u z)) :
    (∫ y in u '' S, complexFormExteriorCoefficient a y)=
      ∫ z in S, complexFormExteriorCoefficient (fun w => a (u w)*deriv u w) z := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume ms
    (fun z hz => ((hol z hz).differentiableAt.restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt) one]
  apply setIntegral_congr_fun ms
  intro z hz
  dsimp only
  rw [holomorphic_real_jacobian (hol z hz).differentiableAt,abs_of_nonneg (sq_nonneg _),
    complex_form_exterior_pullback (hol z hz) (diff z hz)]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_complex_form_stokes
#print axioms TwoAxisHelicoid.complex_form_exterior_integral_pullback
