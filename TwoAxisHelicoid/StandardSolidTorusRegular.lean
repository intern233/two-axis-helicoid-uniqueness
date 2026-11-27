import TwoAxisHelicoid.HorizontalLineCoordinates
import TwoAxisHelicoid.SolidTorusBoundaryCoordinates

namespace TwoAxisHelicoid
open Complex Set Matrix Metric Topology
open scoped ContDiff

/-- The solid torus of major radius two and meridional radius one.
Coordinates are the actual three Euclidean coordinate functions. -/
noncomputable def standardSolidToroidalPoint (u : Circle) (z : ℂ) : Fin 3 → ℝ :=
  ![(2+z.re)*(u:ℂ).re,(2+z.re)*(u:ℂ).im,z.im]

theorem standardSolidToroidalPoint_continuous : Continuous (fun x : Circle × ℂ => standardSolidToroidalPoint x.1 x.2) := by
  apply continuous_pi
  intro j
  fin_cases j <;> dsimp [standardSolidToroidalPoint] <;> fun_prop

theorem standardSolidToroidalPoint_injective_on : InjOn
    (fun x : Circle × ℂ => standardSolidToroidalPoint x.1 x.2) (univ ×ˢ closedBall 0 1) := by
  rintro ⟨a,z⟩ hz ⟨b,w⟩ hw he
  have hrA : -(1:ℝ) ≤ z.re := by
    have h := Complex.abs_re_le_norm z
    have h' : ‖z‖ ≤ 1 := by simpa [mem_closedBall] using hz.2
    linarith [neg_abs_le z.re]
  have hrB : -(1:ℝ) ≤ w.re := by
    have h := Complex.abs_re_le_norm w
    have h' : ‖w‖ ≤ 1 := by simpa [mem_closedBall] using hw.2
    linarith [neg_abs_le w.re]
  have hre : (2+z.re)*(a:ℂ).re = (2+w.re)*(b:ℂ).re := congrFun he 0
  have him : (2+z.re)*(a:ℂ).im = (2+w.re)*(b:ℂ).im := congrFun he 1
  have hv : z.im = w.im := congrFun he 2
  have hxy : ((2+z.re:ℝ):ℂ)*(a:ℂ) = ((2+w.re:ℝ):ℂ)*(b:ℂ)  := by
    apply Complex.ext
    · simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hre
    · simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] using him
  have hN := congrArg norm hxy
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Circle.norm_coe,mul_one,
    abs_of_pos (by linarith : 0 < 2+z.re),abs_of_pos (by linarith : 0 < 2+w.re)] at hN
  have hz' : z = w := Complex.ext (by linarith) hv
  subst w
  have hn : ((2+z.re : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  exact Prod.ext (Subtype.ext (mul_left_cancel₀ hn hxy)) rfl

noncomputable def standardMeridianChart (x : ℝ × ℂ) : Fin 3 → ℝ :=
  ![(2+x.2.re)*Real.cos x.1,(2+x.2.re)*Real.sin x.1,x.2.im]

theorem standardMeridianChart_contDiff : ContDiff ℝ ∞ standardMeridianChart := by
  apply contDiff_pi.mpr
  intro j
  have hr : ContDiff ℝ ∞ (fun x : ℝ × ℂ => 2+x.2.re) :=
    contDiff_const.add (Complex.reCLM.contDiff.comp contDiff_snd)
  fin_cases j
  · exact hr.mul (Real.contDiff_cos.comp contDiff_fst)
  · exact hr.mul (Real.contDiff_sin.comp contDiff_fst)
  · exact Complex.imCLM.contDiff.comp contDiff_snd

theorem standardMeridianChart_fderiv_directions (z : ℂ) (v : ℝ × ℂ) :
    fderiv ℝ standardMeridianChart (0,z) v = ![v.2.re,(2+z.re)*v.1,v.2.im] := by
  let P := ContinuousLinearMap.fst ℝ ℝ ℂ
  let R := Complex.reCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℂ)
  let J := Complex.imCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℂ)
  let r := fun x : ℝ × ℂ => 2+x.2.re
  have hr : HasFDerivAt r R (0,z) := by simpa [r,R] using (R.hasFDerivAt (x := (0,z))).const_add 2
  have hc : HasFDerivAt (fun x : ℝ × ℂ => Real.cos x.1) (0 : (ℝ × ℂ) →L[ℝ] ℝ) (0,z) := by
    simpa [P,Function.comp_def] using! (Real.hasDerivAt_cos 0).comp_hasFDerivAt (0,z) P.hasFDerivAt
  have hs : HasFDerivAt (fun x : ℝ × ℂ => Real.sin x.1) P (0,z) := by
    simpa [P,Function.comp_def] using! (Real.hasDerivAt_sin 0).comp_hasFDerivAt (0,z) P.hasFDerivAt
  have hd := (standardMeridianChart_contDiff.differentiable (by simp) (0,z)).hasFDerivAt
  have hc0 := (hasFDerivAt_pi'.mp hd 0).unique (hr.mul hc)
  have hc1 := (hasFDerivAt_pi'.mp hd 1).unique (hr.mul hs)
  have hc2 := (hasFDerivAt_pi'.mp hd 2).unique (J.hasFDerivAt (x := (0,z)))
  funext i
  fin_cases i
  · simpa [r,R,P] using congrArg (fun D : (ℝ × ℂ) →L[ℝ] ℝ => D v) hc0
  · simpa [r,R,P] using congrArg (fun D : (ℝ × ℂ) →L[ℝ] ℝ => D v) hc1
  · exact congrArg (fun D : (ℝ × ℂ) →L[ℝ] ℝ => D v) hc2

theorem standardMeridianChart_fderiv_injective {z : ℂ} (hz : z ∈ closedBall (0:ℂ) 1) :
    Function.Injective (fderiv ℝ standardMeridianChart (0,z)) := by
  have hc : ‖z‖ ≤ 1 := by simpa [mem_closedBall] using hz
  have hr : 2+z.re ≠ 0 := by linarith [Complex.abs_re_le_norm z,neg_abs_le z.re]
  intro u v he
  rw [standardMeridianChart_fderiv_directions,standardMeridianChart_fderiv_directions] at he
  exact Prod.ext (mul_left_cancel₀ hr (congrFun he 1)) (Complex.ext (congrFun he 0) (congrFun he 2))

/-- The longitude chart at any meridian differs from the chart at the
positive real meridian by an actual Euclidean rotation. -/
theorem standardToroid_longitude_formula (a : Circle) (x : ℝ × ℂ) :
    standardSolidToroidalPoint (Circle.exp x.1*a) x.2 =
      unitVerticalRotation (a:ℂ) a.norm_coe (standardMeridianChart x) := by
  funext j
  fin_cases j <;> simp [standardSolidToroidalPoint,standardMeridianChart,unitVerticalRotation,
    verticalRotation_apply,Circle.coe_mul,Circle.coe_exp,Complex.mul_re,Complex.mul_im,Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im] <;> ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.standardSolidToroidalPoint_injective_on
#print axioms TwoAxisHelicoid.standardMeridianChart_fderiv_injective
#print axioms TwoAxisHelicoid.standardToroid_longitude_formula
