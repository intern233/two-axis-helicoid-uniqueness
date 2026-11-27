import TwoAxisHelicoid.DiskGeneratorHalfPlane
import TwoAxisHelicoid.FlatCylinderExponential
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology

theorem deriv_nonzero_of_analytic_left_inverse {F G : ℂ → ℂ} {z : ℂ} (f : AnalyticAt ℂ F z)
    (g : AnalyticAt ℂ G (F z)) (left : G ∘ F =ᶠ[𝓝 z] id) : deriv F z≠0 := by
  have eq := (g.differentiableAt.hasDerivAt.comp z f.differentiableAt.hasDerivAt).deriv
  rw [left.deriv_eq,deriv_id] at eq
  intro h
  rw [h,mul_zero] at eq
  exact one_ne_zero eq

theorem boundaryCayley_regular {u z : ℂ} (hu : ‖u‖=1) (hz : ‖z‖<1) :
    AnalyticAt ℂ (boundaryCayley u) z ∧ deriv (boundaryCayley u) z≠0 := by
  have a := boundaryCayley_analytic hu hz
  refine ⟨a,deriv_nonzero_of_analytic_left_inverse a (boundaryCayleyInv_analytic (u := u) (boundaryCayley_right hu hz)) ?_⟩
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw using boundaryCayley_left_inv hu hw

theorem boundaryCayley_exact_range {u : ℂ} (hu : ‖u‖=1) :
    boundaryCayley u '' complexUnitDisk={w : ℂ | 0<w.re} := by
  ext w
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact boundaryCayley_right hu (by simpa only [complexUnitDisk,mem_ball,dist_zero_right] using hz)
  · intro pos
    refine ⟨boundaryCayleyInv u w,?_,boundaryCayley_right_inv hu pos⟩
    simpa only [complexUnitDisk,mem_ball,dist_zero_right] using boundaryCayleyInv_disk hu pos

theorem right_half_log_range (b : ℝ) :
    (fun w : ℂ => Complex.log (w-(b:ℂ)*I)) '' {w : ℂ | 0<w.re}={z : ℂ | |z.im|<Real.pi/2} := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    change |(Complex.log (w-(b:ℂ)*I)).im|<Real.pi/2
    rw [Complex.log_im,Complex.abs_arg_lt_pi_div_two_iff]
    exact Or.inl (by simpa using hw)
  · intro h
    have bds := abs_lt.mp (show |z.im|<Real.pi/2 from h)
    have pos : 0<(Complex.exp z).re := by rw [Complex.exp_re]; exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo bds)
    refine ⟨Complex.exp z+(b:ℂ)*I,?_,?_⟩
    · change 0<(Complex.exp z+(b:ℂ)*I).re
      simpa using pos
    · change Complex.log ((Complex.exp z+(b:ℂ)*I)-(b:ℂ)*I)=z
      rw [add_sub_cancel_right,Complex.log_exp (by linarith [Real.pi_pos,bds.1]) (by linarith [Real.pi_pos,bds.2])]

noncomputable def boundaryLogCoordinate (u : ℂ) (b : ℝ) (z : ℂ) :=
  Complex.log (boundaryCayley u z-(b:ℂ)*I)

theorem boundaryLogCoordinate_range {u : ℂ} (hu : ‖u‖=1) (b : ℝ) :
    boundaryLogCoordinate u b '' complexUnitDisk={z : ℂ | |z.im|<Real.pi/2} := by
  change ((fun w : ℂ => Complex.log (w-(b:ℂ)*I)) ∘ boundaryCayley u) '' _=_
  rw [image_comp,boundaryCayley_exact_range hu,right_half_log_range]

theorem boundaryLogCoordinate_regular {u z : ℂ} (hu : ‖u‖=1) (b : ℝ) (hz : ‖z‖<1) :
    AnalyticAt ℂ (boundaryLogCoordinate u b) z ∧ deriv (boundaryLogCoordinate u b) z≠0 := by
  let W := fun x => boundaryCayley u x-(b:ℂ)*I
  have right : 0<(W z).re := by simpa [W] using boundaryCayley_right hu hz
  have ar : AnalyticAt ℂ (boundaryLogCoordinate u b) z :=
    (analyticAt_clog (Or.inl right)).comp ((boundaryCayley_analytic hu hz).sub analyticAt_const)
  let G := fun w => boundaryCayleyInv u (Complex.exp w+(b:ℂ)*I)
  have undo {x : ℂ} (hx : ‖x‖<1) : Complex.exp (boundaryLogCoordinate u b x)+(b:ℂ)*I=boundaryCayley u x := by
    rw [boundaryLogCoordinate,Complex.exp_log,sub_add_cancel]
    intro eq
    have re := congrArg Complex.re eq
    simp at re
    exact (boundaryCayley_right hu hx).ne' re
  have g : AnalyticAt ℂ G (boundaryLogCoordinate u b z) :=
    (boundaryCayleyInv_analytic (u := u) ((undo hz).symm ▸ boundaryCayley_right hu hz)).comp (analyticAt_cexp.add analyticAt_const)
  refine ⟨ar,deriv_nonzero_of_analytic_left_inverse ar g ?_⟩
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with x hx
  change boundaryCayleyInv u (Complex.exp (boundaryLogCoordinate u b x)+_) = x
  rw [undo hx,boundaryCayley_left_inv hu hx]

theorem boundaryLogCoordinate_injOn {u : ℂ} (hu : ‖u‖=1) (b : ℝ) : InjOn (boundaryLogCoordinate u b) complexUnitDisk := by
  intro x hx y hy eq
  have small {z : ℂ} (h : z∈complexUnitDisk) : ‖z‖<1 := by simpa only [complexUnitDisk,mem_ball,dist_zero_right] using h
  have nz (z : ℂ) (hz : z∈complexUnitDisk) : boundaryCayley u z-(b:ℂ)*I≠0 := by
    intro zero
    have re := congrArg Complex.re zero
    simp at re
    exact (boundaryCayley_right hu (small hz)).ne' re
  have h := congrArg Complex.exp eq
  change Complex.exp (Complex.log _)=Complex.exp (Complex.log _) at h
  rw [Complex.exp_log (nz x hx),Complex.exp_log (nz y hy)] at h
  have same := sub_left_inj.mp h
  exact (boundaryCayley_left_inv hu (small hx)).symm.trans ((congrArg (boundaryCayleyInv u) same).trans (boundaryCayley_left_inv hu (small hy)))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.boundaryLogCoordinate_regular
