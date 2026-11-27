import TwoAxisHelicoid.PhysicalLevelThetaPhase
import TwoAxisHelicoid.ObliqueThetaEdgeSound
import TwoAxisHelicoid.TorusThetaDirection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace TwoAxisHelicoid
open Complex Set

noncomputable def transverseBoundaryHeight (a : ℝ) : ℝ := Real.arctan (4/7)/(2*(1-a))

theorem transverse_boundary_height_bounds {a : ℝ} (lo : 1/2≤a) (hi : a<1) :
    1/4<transverseBoundaryHeight a ∧ transverseBoundaryHeight a<1/(2*(1-a)) := by
  let θ := Real.arctan (4/7)
  have pos : 0<θ := Real.arctan_pos.mpr (by norm_num)
  have lead : 1/4<θ := by
    have rad := Real.sq_sqrt (by norm_num : (0:ℝ)≤1+(4/7:ℝ)^2)
    have bound : Real.sqrt (1+(4/7:ℝ)^2)≤2 := by nlinarith
    have rp : 0<Real.sqrt (1+(4/7:ℝ)^2) := by positivity
    have h : 1/4<Real.sin θ := by
      rw [show Real.sin θ=(4/7)/Real.sqrt (1+(4/7:ℝ)^2) from Real.sin_arctan _]
      apply (lt_div_iff₀ rp).mpr
      linarith
    exact h.trans_le (Real.sin_le pos.le)
  have up : θ<1 := (Real.arctan_lt_self (by norm_num : (0:ℝ)<4/7)).trans (by norm_num)
  have den : 0<2*(1-a) := by linarith
  exact ⟨(lt_div_iff₀ den).mpr (by nlinarith),div_lt_div_of_pos_right up den⟩

/-- At this physical height the oblique test is exactly the sign of the
second, unrotated spatial component of the horizontal tangent. -/
theorem transverse_boundary_gauss_sign {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (root : thetaG t a=0)
    {z : ℂ} (height : (actualComplexHeight t a 1 ht z).re=transverseBoundaryHeight a)
    (direction : (obliqueThetaFactor true*torusThetaDirection t a z).re<0) :
    (thetaGauss t a 1 z).re<0 := by
  let θ := Real.arctan (4/7)
  let T := torusThetaDirection t a z
  let H := actualComplexHeight t a 1 ht z
  let b := Real.exp (-(2*(a-1))*H.im)*Real.exp (2*(1-a)*Real.pi/t*z.re)
  have bp : 0<b := mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have e : 2*(a-1)*transverseBoundaryHeight a= -θ := by
    dsimp [transverseBoundaryHeight,θ]
    field_simp [sub_ne_zero.mpr (ne_of_gt ha.2)]; ring
  have val := physical_level_gauss_theta_ratio ht ha root z
  dsimp only at val
  rw [height,e,theta_ratio_torus_direction] at val
  have form : thetaGauss t a 1 z= (I*exp ((-(θ:ℂ))*I))*(b:ℂ)*T := by
    rw [val]
    dsimp only [b,H,T]
    push_cast
    ring_nf
  have sine : Real.sin θ=4/7*Real.cos θ := by
    rw [← Real.tan_mul_cos (Real.cos_arctan_pos _).ne',Real.tan_arctan]
  have coeff : 4*T.re-7*T.im<0 := by simpa [obliqueThetaFactor,T,Complex.mul_re] using direction
  have alg : (thetaGauss t a 1 z).re=b*(Real.cos θ/7)*(4*T.re-7*T.im) := by
    rw [form]
    simp only [← ofReal_neg,Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im,Complex.mul_re,
      Complex.mul_im,ofReal_re,ofReal_im,I_re,I_im,Real.cos_neg,Real.sin_neg]
    rw [sine]
    ring
  rw [alg]
  exact mul_neg_of_pos_of_neg (mul_pos bp (div_pos (Real.cos_arctan_pos _) (by norm_num))) coeff

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.transverse_boundary_height_bounds
#print axioms TwoAxisHelicoid.transverse_boundary_gauss_sign
