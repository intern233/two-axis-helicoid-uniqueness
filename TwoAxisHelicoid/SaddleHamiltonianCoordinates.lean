import TwoAxisHelicoid.ConformalPlaneColumns
import TwoAxisHelicoid.ConformalPlaneDistortion
import Mathlib.Analysis.Calculus.Gradient.Basic

namespace TwoAxisHelicoid
open Complex Filter Topology Function InnerProductSpace
open scoped Topology ContDiff RealInnerProductSpace ComplexConjugate

/-- Signed Jacobian of the two product coordinates of a saddle, in the
global real basis 1,i of the covering plane. -/
noncomputable def saddleCoordinateJacobian (u v : ℂ → ℝ) (z : ℂ) : ℝ :=
  fderiv ℝ u z 1*fderiv ℝ v z I-fderiv ℝ u z I*fderiv ℝ v z 1

private theorem gradient_real_columns (h : ℂ → ℝ) (z : ℂ) :
    (gradient h z).re=fderiv ℝ h z 1 ∧ (gradient h z).im=fderiv ℝ h z I := by
  constructor
  · rw [← inner_gradient_left,real_inner_eq_re_inner ℂ,RCLike.inner_apply]
    change (gradient h z).re=((1:ℂ)*conj (gradient h z)).re
    simp
  · rw [← inner_gradient_left,real_inner_eq_re_inner ℂ,RCLike.inner_apply]
    change (gradient h z).im=(I*conj (gradient h z)).re
    simp

/-- In a genuine product germ h=c+uv the physical rotated gradient
drives the two coordinates with opposite logarithmic rates. This
identity also holds directly on both coordinate axes. -/
theorem rotated_gradient_in_saddle_coordinates {h u v : ℂ → ℝ} {z : ℂ} {c : ℝ}
    (du : DifferentiableAt ℝ u z) (dv : DifferentiableAt ℝ v z)
    (germ : h =ᶠ[𝓝 z] fun w => c+u w*v w) :
    fderiv ℝ u z (I*gradient h z)= -saddleCoordinateJacobian u v z*u z ∧
      fderiv ℝ v z (I*gradient h z)=saddleCoordinateJacobian u v z*v z := by
  have derivative := (hasFDerivAt_const c z).add (du.hasFDerivAt.mul dv.hasFDerivAt)
  have rate (w : ℂ) : fderiv ℝ h z w=u z*fderiv ℝ v z w+v z*fderiv ℝ u z w := by
    rw [germ.fderiv_eq]
    change (fderiv ℝ ((fun _ => c)+u*v) z) w=_
    rw [derivative.fderiv]
    simp
  obtain ⟨re,im⟩ := gradient_real_columns h z
  constructor
  · rw [real_complex_map_columns (fderiv ℝ u z),Complex.I_mul_re,Complex.I_mul_im,re,im,rate,rate]
    dsimp only [saddleCoordinateJacobian,smul_eq_mul]
    ring
  · rw [real_complex_map_columns (fderiv ℝ v z),Complex.I_mul_re,Complex.I_mul_im,re,im,rate,rate]
    dsimp only [saddleCoordinateJacobian,smul_eq_mul]
    ring

/-- The product-chart Jacobian has one fixed nonzero sign on a
neighborhood of the critical point. Both coordinate derivatives are
taken from the actual parametrization. -/
theorem saddle_coordinate_jacobian_fixed_sign {q : ℂ → ℝ×ℝ} {z : ℂ}
    (smooth : ContDiffAt ℝ 1 q z) (inj : Injective (fderiv ℝ q z)) :
    let u := Prod.fst ∘ q
    let v := Prod.snd ∘ q
    saddleCoordinateJacobian u v z≠0 ∧
      ∀ᶠ w in 𝓝 z, 0<saddleCoordinateJacobian u v z*saddleCoordinateJacobian u v w := by
  let u := Prod.fst ∘ q
  let v := Prod.snd ∘ q
  let D := fderiv ℝ q z
  let A := Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp D
  have df := (smooth.differentiableAt one_ne_zero).hasFDerivAt
  have uD : fderiv ℝ u z=(ContinuousLinearMap.fst ℝ ℝ ℝ).comp D := (hasFDerivAt_fst.comp z df).fderiv
  have vD : fderiv ℝ v z=(ContinuousLinearMap.snd ℝ ℝ ℝ).comp D := (hasFDerivAt_snd.comp z df).fderiv
  have eq : saddleCoordinateJacobian u v z=A.det := by
    rw [complex_real_det_eq,saddleCoordinateJacobian,uD,vD]
    change (D 1).1*(D I).2-(D I).1*(D 1).2=(D 1).1*(D I).2-(D 1).2*(D I).1
    ring
  have regular : Injective A := Complex.equivRealProdCLM.symm.injective.comp inj
  have nz : saddleCoordinateJacobian u v z≠0 := by
    rw [eq]
    exact (LinearEquiv.ofInjectiveEndo A.toLinearMap regular).isUnit_det'.ne_zero
  have su : ContDiffAt ℝ 1 u z := contDiff_fst.contDiffAt.comp z smooth
  have sv : ContDiffAt ℝ 1 v z := contDiff_snd.contDiffAt.comp z smooth
  have cu (w : ℂ) := (su.continuousAt_fderiv one_ne_zero).clm_apply (continuousAt_const (y:=w))
  have cv (w : ℂ) := (sv.continuousAt_fderiv one_ne_zero).clm_apply (continuousAt_const (y:=w))
  have cj : ContinuousAt (saddleCoordinateJacobian u v) z :=
    ((cu 1).mul (cv I)).sub ((cu I).mul (cv 1))
  exact ⟨nz,(continuousAt_const.mul cj).eventually (Ioi_mem_nhds (mul_self_pos.mpr nz))⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rotated_gradient_in_saddle_coordinates
#print axioms TwoAxisHelicoid.saddle_coordinate_jacobian_fixed_sign
