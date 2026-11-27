import TwoAxisHelicoid.LeftComparisonFunction
import Mathlib.Analysis.Complex.HasPrimitives

namespace TwoAxisHelicoid
open Complex Set Metric
set_option maxHeartbeats 800000

noncomputable def leftMobius (x : ℂ) : ℂ := I*(x+1)/(x-1)

noncomputable def leftChordDifferential (t k : ℝ) (u : ℂ) : ℂ :=
  (I*(Real.pi : ℂ)/(2*(t : ℂ)))*((u+I)/(u-I))*Complex.exp (I*(k : ℂ)*u)

theorem leftMobius_sub_I {x : ℂ} (hx : x ≠ 1) :
    leftMobius x-I = 2*I/(x-1) := by
  unfold leftMobius
  field_simp [sub_ne_zero.mpr hx]
  ring

theorem leftMobius_ne_I {x : ℂ} (hx : x ≠ 1) : leftMobius x ≠ I := by
  apply sub_ne_zero.mp
  rw [leftMobius_sub_I hx]
  exact div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (sub_ne_zero.mpr hx)

theorem leftMobius_ratio {x : ℂ} (hx : x ≠ 1) :
    (leftMobius x+I)/(leftMobius x-I) = x := by
  rw [leftMobius_sub_I hx]
  unfold leftMobius
  field_simp [sub_ne_zero.mpr hx, I_ne_zero]
  ring

theorem I_mul_leftMobius {x : ℂ} (hx : x ≠ 1) :
    I*leftMobius x = -1+2/(1-x) := by
  unfold leftMobius
  field_simp [sub_ne_zero.mpr hx, sub_ne_zero.mpr hx.symm]
  simp only [I_sq]
  ring

theorem leftMobius_hasDerivAt {x : ℂ} (hx : x ≠ 1) :
    HasDerivAt leftMobius (-2*I/(x-1)^2) x := by
  have h := (((hasDerivAt_id x).add_const 1).const_mul I).div
    ((hasDerivAt_id x).sub_const 1) (sub_ne_zero.mpr hx)
  convert h using 1
  · rfl
  · simp only [id_eq, mul_one]
    ring

theorem leftComparisonFunction_mobius {t : ℝ} (ht : 0 < t) {w : ℂ}
    (hx : jacobiExp w ≠ 1) :
    leftComparisonFunction t w =
      leftChordDifferential t (dualProductKappa t (verticalA t)) (leftMobius (jacobiExp w))*
        ((-2*I/(jacobiExp w-1)^2)*(I*(Real.pi : ℂ)*jacobiExp w)) := by
  have he : I*(dualProductKappa t (verticalA t) : ℂ)*leftMobius (jacobiExp w) =
      (dualProductKappa t (verticalA t) : ℂ)*(-1+2/(1-jacobiExp w)) := by
    rw [mul_right_comm, I_mul_leftMobius hx]
    ring
  unfold leftChordDifferential
  rw [leftMobius_ratio hx, he]
  unfold leftComparisonFunction dualProductMainTerm
  field_simp [Complex.ofReal_ne_zero.mpr ht.ne',
    sub_ne_zero.mpr hx, sub_ne_zero.mpr hx.symm]
  simp only [I_sq]
  ring

theorem leftChordDifferential_differentiableAt (t k : ℝ) {u : ℂ} (hu : u ≠ I) :
    DifferentiableAt ℂ (leftChordDifferential t k) u := by
  unfold leftChordDifferential
  apply DifferentiableAt.mul
  · exact ((differentiableAt_id.add_const I).div
      (differentiableAt_id.sub_const I) (sub_ne_zero.mpr hu)).const_mul _
  · fun_prop

theorem leftChordDifferential_exact_ball (t k : ℝ) {R : ℝ} (hR : 0 < R) :
    Complex.IsExactOn (leftChordDifferential t k) (ball (R : ℂ) R) := by
  apply DifferentiableOn.isExactOn_ball
  intro u hu
  apply (leftChordDifferential_differentiableAt t k ?_).differentiableWithinAt
  intro he
  subst u
  have hd : ‖I-(R : ℂ)‖ < R := mem_ball_iff_norm.mp hu
  have hs := Complex.sq_norm (I-(R : ℂ))
  simp only [normSq_apply, sub_re, I_re, ofReal_re, sub_im, I_im, ofReal_im,
    sub_zero, zero_sub] at hs
  have hn := norm_nonneg (I-(R : ℂ))
  nlinarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.leftComparisonFunction_mobius
#print axioms TwoAxisHelicoid.leftChordDifferential_exact_ball
