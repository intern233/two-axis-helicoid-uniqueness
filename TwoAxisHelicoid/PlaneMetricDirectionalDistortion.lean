import TwoAxisHelicoid.ConformalPlaneDistortion
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace TwoAxisHelicoid
open Complex

/-- The same determinant bound holds for every direction in the plane,
including the angular tangent used in the annulus area estimate. -/
theorem directional_distortion_of_conformal_bounds (L : ℂ →L[ℝ] ℂ) {m c : ℝ} (hm : 0<m)
    (metric : ∀ w : ℂ, m*‖L w‖^2/4≤c*‖w‖^2 ∧ c*‖w‖^2≤4*(m*‖L w‖^2)) (v : ℂ) :
    ‖L v‖^2≤4*|L.det| *‖v‖^2 := by
  let S := ((ContinuousLinearMap.id ℂ ℂ).smulRight v).restrictScalars ℝ
  have app (w : ℂ) : S w=w*v := rfl
  have det : S.det=‖v‖^2 := by
    rw [complex_real_det_eq,planeRealJacobian,app,app,one_mul,Complex.I_mul_re,Complex.I_mul_im,
      Complex.sq_norm,Complex.normSq_apply]
    ring
  have mt (w : ℂ) := metric (S w)
  have b := horizontal_distortion_of_conformal_bounds (L.comp S) (c := c*‖v‖^2) hm (fun w => by
    have h := mt w
    have n : c*‖S w‖^2=(c*‖v‖^2)*‖w‖^2 := by rw [app,norm_mul,mul_pow]; ring
    rwa [n] at h)
  have comp : (L.comp S).det=L.det*S.det := LinearMap.det_comp _ _
  have one : (L.comp S) 1=L v := by rw [ContinuousLinearMap.comp_apply,app,one_mul]
  rw [one,comp,det,abs_mul,abs_of_nonneg (sq_nonneg ‖v‖)] at b
  simpa only [mul_assoc] using b

/-- A plane coordinate with two-sided metric bounds has a differentiable
local inverse at every regular point, with the same distortion constant. -/
theorem inverse_coordinate_distortion (e : OpenPartialHomeomorph ℂ ℂ) {y : ℂ} (hy : y∈e.target)
    (smooth : ContDiffAt ℝ 1 e (e.symm y)) {m c : ℝ} (_hm : 0<m) (hc : 0<c)
    (metric : ∀ w : ℂ, m*‖fderiv ℝ e (e.symm y) w‖^2/4≤c*‖w‖^2 ∧
      c*‖w‖^2≤4*(m*‖fderiv ℝ e (e.symm y) w‖^2)) :
    ContDiffAt ℝ 1 e.symm y ∧ ∀ v : ℂ, ‖fderiv ℝ e.symm y v‖^2≤4*|(fderiv ℝ e.symm y).det| *‖v‖^2 := by
  let L := fderiv ℝ e (e.symm y)
  have inj : Function.Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    intro w zero
    have b := (metric w).2
    change c*‖w‖^2≤4*(m*‖L w‖^2) at b
    rw [zero,norm_zero] at b
    by_contra nw
    have nz := mul_pos hc (pow_pos (norm_pos_iff.mpr nw) 2)
    linarith
  let T := (LinearEquiv.ofInjectiveEndo L.toLinearMap inj).toContinuousLinearEquiv
  have d : HasFDerivAt e (T : ℂ →L[ℝ] ℂ) (e.symm y) := (smooth.differentiableAt one_ne_zero).hasFDerivAt
  have inv := e.hasFDerivAt_symm hy d
  refine ⟨e.contDiffAt_symm hy d smooth,?_⟩
  rw [inv.fderiv]
  apply directional_distortion_of_conformal_bounds _ (m := c) (c := m) hc
  intro w
  have bound := metric (T.symm w)
  change m*‖T (T.symm w)‖^2/4≤c*‖T.symm w‖^2 ∧ c*‖T.symm w‖^2≤4*(m*‖T (T.symm w)‖^2) at bound
  rw [T.apply_symm_apply] at bound
  change c*‖T.symm w‖^2/4≤m*‖w‖^2 ∧ m*‖w‖^2≤4*(c*‖T.symm w‖^2)
  constructor <;> linarith [bound.1,bound.2]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.inverse_coordinate_distortion
