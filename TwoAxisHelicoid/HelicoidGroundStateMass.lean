import TwoAxisHelicoid.SchrodingerTensorEnergy
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace TwoAxisHelicoid

open Real MeasureTheory Set Filter Topology
open scoped ContDiff

theorem helicoidGroundState_pos_le_one (x : ℝ) :
    0<helicoidGroundState x ∧ helicoidGroundState x≤1 := by
  refine ⟨inv_pos.mpr (Real.cosh_pos x),?_⟩
  change (Real.cosh x)⁻¹≤1
  simpa only [one_div] using (div_le_one (Real.cosh_pos x)).mpr (Real.one_le_cosh x)

theorem helicoidGroundState_smooth : ContDiff ℝ ∞ helicoidGroundState := by
  unfold helicoidGroundState
  fun_prop (disch := intros; positivity)

theorem helicoidGroundState_deriv_abs (x : ℝ) :
    |deriv helicoidGroundState x|≤helicoidGroundState x := by
  have eq : deriv helicoidGroundState x = -(Real.tanh x)*helicoidGroundState x := by
    rw [helicoidGroundState_deriv,Real.tanh_eq_sinh_div_cosh]
    dsimp [helicoidGroundState]
    field_simp [(Real.cosh_pos x).ne']
  rw [eq,abs_mul,abs_neg,abs_of_pos (helicoidGroundState_pos_le_one x).1]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (Real.abs_tanh_lt_one x).le
    (helicoidGroundState_pos_le_one x).1.le

private theorem ground_tanh_top : Tendsto Real.tanh atTop (𝓝 1) := by
  let r := fun y : ℝ => (1-y^2)/(1+y^2)
  have c : Continuous r := by dsimp [r]; fun_prop (disch := intros; positivity)
  have v := (c.continuousAt (x:=0)).tendsto.comp Real.tendsto_exp_neg_atTop_nhds_zero
  rw [show r 0=1 by norm_num [r]] at v
  apply v.congr
  intro x
  change (1-Real.exp (-x)^2)/(1+Real.exp (-x)^2)=Real.tanh x
  rw [Real.tanh_eq]
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  rw [Real.exp_neg]
  field_simp [(Real.exp_pos x).ne']

/-- On the whole real line the squared transverse state has integral two.
The exact Jacobi energy density has integral minus two. -/
theorem helicoidGroundState_mass_and_energy :
    Integrable (fun x : ℝ => helicoidGroundState x^2) ∧
    (∫ x : ℝ, helicoidGroundState x^2)=2 ∧
    Integrable helicoidGroundEnergyDensity ∧ (∫ x : ℝ, helicoidGroundEnergyDensity x)= -2 := by
  let f := helicoidGroundState
  have cs : Continuous (fun x : ℝ => f x^2) := helicoidGroundState_smooth.continuous.pow 2
  have d (x : ℝ) : HasDerivAt Real.tanh (f x^2) x := by
    simpa only [f,helicoidGroundState,inv_pow,one_div] using real_tanh_hasDerivAt x
  have int : Integrable (fun x : ℝ => f x^2) := by
    apply integrable_of_intervalIntegral_norm_bounded (a:=fun x : ℝ => -x) (b:=id) 2
      (fun x => (cs.intervalIntegrable _ _).1) tendsto_neg_atTop_atBot tendsto_id
    filter_upwards with R
    simp only [id_eq,Real.norm_eq_abs,abs_sq]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => d x) (cs.intervalIntegrable _ _),Real.tanh_neg]
    linarith [Real.tanh_lt_one R]
  have bottom : Tendsto Real.tanh atBot (𝓝 (-1)) := by
    simpa only [Function.comp_def,Real.tanh_neg,neg_neg] using (ground_tanh_top.comp tendsto_neg_atBot_atTop).neg
  have mass := integral_of_hasDerivAt_of_tendsto d int bottom ground_tanh_top
  have energy : Integrable helicoidGroundEnergyDensity := by
    refine (int.const_mul 3).mono' helicoidGroundEnergyDensity_continuous.aestronglyMeasurable (ae_of_all _ ?_)
    intro x
    have h := helicoidGroundState_pos_le_one x
    have derivsq : (deriv helicoidGroundState x)^2≤helicoidGroundState x^2 := sq_le_sq.mpr (by rw [abs_of_pos h.1]; exact helicoidGroundState_deriv_abs x)
    have msq : f x^2≤1 := by simpa only [one_pow] using pow_le_pow_left₀ h.1.le h.2 2
    have fourth : f x^4≤f x^2 := by nlinarith [mul_nonneg (sq_nonneg (f x)) (sub_nonneg.mpr msq)]
    change ‖(deriv f x)^2-2*(f x)^4‖≤3*(f x)^2
    rw [Real.norm_eq_abs]
    have tri := abs_sub_le ((deriv f x)^2) 0 (2*(f x)^4)
    simp only [sub_zero,zero_sub,abs_neg] at tri
    rw [abs_sq (deriv f x),abs_of_nonneg (by positivity : 0≤2*f x^4)] at tri
    change (deriv f x)^2≤(f x)^2 at derivsq
    linarith
  have lo := (bottom.pow 3).sub (bottom.const_mul 2)
  have hi := (ground_tanh_top.pow 3).sub (ground_tanh_top.const_mul 2)
  have total := integral_of_hasDerivAt_of_tendsto helicoidGroundEnergy_primitive energy lo hi
  exact ⟨int,by linarith,energy,by norm_num at total; exact total⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.helicoidGroundState_mass_and_energy
