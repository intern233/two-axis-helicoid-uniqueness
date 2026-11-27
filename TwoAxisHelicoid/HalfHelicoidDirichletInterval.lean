import TwoAxisHelicoid.HelicoidGroundState
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace TwoAxisHelicoid
open Real Set MeasureTheory Filter Topology
open scoped Topology ContDiff

/-- The one-dimensional ground-state transform on a closed interval.
The test function satisfies ordinary pointwise Dirichlet conditions.
The comparison function is allowed to be nonconstant at the boundary. -/
theorem interval_energy_of_positive_jacobi_solution {a b : ℝ} (ab : a≤b) {f w u V : ℝ → ℝ}
    (smooth : ContDiff ℝ 1 f) (cw : Continuous w) (cu : Continuous u) (cV : Continuous V)
    (dw : ∀ x∈Icc a b, HasDerivAt w (u x) x)
    (du : ∀ x∈Icc a b, HasDerivAt u (-(V x*w x)) x)
    (pos : ∀ x∈Icc a b, 0<w x) (left : f a=0) (right : f b=0) :
    0≤∫ x in a..b, (deriv f x)^2-V x*(f x)^2 := by
  let E := fun x => (deriv f x)^2-V x*(f x)^2
  let D := fun x => E x-(deriv f x-u x/w x*f x)^2
  let H := fun x => u x/w x*f x^2
  have cdf : Continuous (deriv f) := smooth.continuous_deriv le_rfl
  have cE : Continuous E := (cdf.pow 2).sub (cV.mul (smooth.continuous.pow 2))
  have cD : ContinuousOn D (Icc a b) := cE.continuousOn.sub ((cdf.continuousOn.sub
    ((cu.continuousOn.div cw.continuousOn fun x hx => (pos x hx).ne').mul smooth.continuous.continuousOn)).pow 2)
  have primitive (x : ℝ) (hx : x∈uIcc a b) : HasDerivAt H (D x) x := by
    rw [uIcc_of_le ab] at hx
    have df := ((smooth.differentiable (by simp)) x).hasDerivAt
    convert (((du x hx).div (dw x hx) (pos x hx).ne').mul (df.pow 2)) using 1
    dsimp [D,E]
    field_simp [(pos x hx).ne']
    ring
  have iD := cD.intervalIntegrable_of_Icc (μ:=volume) ab
  have h := intervalIntegral.integral_mono_on ab iD (cE.intervalIntegrable _ _)
    (fun x _ => sub_le_self (E x) (sq_nonneg _))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt primitive iD] at h
  simpa only [H,left,right,zero_pow (by decide : 2≠0),mul_zero,sub_zero] using h

/-- Dirichlet stability on the complete transverse half-line, restricted
to any finite interval starting at the axis. Translating the positive
Jacobi field tanh by δ makes it positive at the boundary; the quadratic
forms converge as δ decreases to zero. -/
theorem half_helicoid_transverse_interval_nonnegative {b : ℝ} (bp : 0≤b) {f : ℝ → ℝ}
    (smooth : ContDiff ℝ 1 f) (axis : f 0=0) (edge : f b=0) :
    0≤∫ x in (0:ℝ)..b, (deriv f x)^2-2*(Real.cosh x)⁻¹^2*(f x)^2 := by
  let E := fun (δ x : ℝ) => (deriv f x)^2-2*(Real.cosh (x+δ))⁻¹^2*f x^2
  have df : Continuous (deriv f) := smooth.continuous_deriv le_rfl
  have cont : Continuous (Function.uncurry E) := by
    change Continuous (fun p : ℝ × ℝ => (deriv f p.2)^2-2*(Real.cosh (p.2+p.1))⁻¹^2*(f p.2)^2)
    fun_prop (disch := intros; positivity)
  have lim := (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ:=volume) cont 0 b).continuousAt (x:=0)
  have lower (δ : ℝ) (positive : 0<δ) : 0≤∫ x in (0:ℝ)..b, E δ x := by
    let w := fun x : ℝ => Real.tanh (x+δ)
    let u := fun x : ℝ => 1/(Real.cosh (x+δ))^2
    let V := fun x : ℝ => 2*(Real.cosh (x+δ))⁻¹^2
    have dw (x : ℝ) : HasDerivAt w (u x) x := by
      simpa only [w,u,Function.comp_def,mul_one] using (real_tanh_hasDerivAt (x+δ)).comp x ((hasDerivAt_id' x).add_const δ)
    have du (x : ℝ) : HasDerivAt u (-(V x*w x)) x := by
      have c := (Real.hasDerivAt_cosh (x+δ)).comp x ((hasDerivAt_id' x).add_const δ)
      have d := (hasDerivAt_const x (1:ℝ)).div (c.pow 2) (pow_ne_zero 2 (Real.cosh_pos _).ne')
      have fdef : (fun y : ℝ => 1)/(Real.cosh ∘ fun y : ℝ => y+δ)^2=u := by funext y; rfl
      rw [fdef] at d
      apply d.congr_deriv
      simp only [w,V,Function.comp_apply,Pi.pow_apply,Real.tanh_eq_sinh_div_cosh]
      field_simp [(Real.cosh_pos (x+δ)).ne']
      ring
    apply interval_energy_of_positive_jacobi_solution (w:=w) (u:=u) (V:=V) bp smooth
      (continuous_iff_continuousAt.mpr fun x => (dw x).continuousAt)
      (continuous_iff_continuousAt.mpr fun x => (du x).continuousAt)
      (by dsimp [V]; fun_prop (disch := intros; positivity))
      (fun x _ => dw x) (fun x _ => du x) _ axis edge
    intro x hx
    rw [show w x=Real.sinh (x+δ)/Real.cosh (x+δ) from Real.tanh_eq_sinh_div_cosh _]
    exact div_pos (Real.sinh_pos_iff.mpr (add_pos_of_nonneg_of_pos hx.1 positive)) (Real.cosh_pos _)
  have zero := ge_of_tendsto (lim.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0))
    (show ∀ᶠ δ in 𝓝[>] (0:ℝ), 0≤∫ x in (0:ℝ)..b,E δ x by
      filter_upwards [self_mem_nhdsWithin (s:=Ioi (0:ℝ)) (a:=0)] with δ hδ using lower δ hδ)
  simpa only [E,add_zero] using zero

/-- A Dirichlet test on a bounded axial interval gains an explicit
positive spectral gap. The positive cosine comparison stays away from
zero at both endpoints. -/
theorem half_helicoid_axial_interval_gap {R : ℝ} (rp : 0<R) {f : ℝ → ℝ}
    (smooth : ContDiff ℝ 1 f) (left : f (-R)=0) (right : f R=0) :
    0≤∫ x in (-R)..R, (deriv f x)^2-(1/(R+1))^2*(f x)^2 := by
  let k := 1/(R+1)
  have kp : 0<k := by dsimp [k]; positivity
  let w := fun x : ℝ => Real.cos (k*x)
  let u := fun x : ℝ => -Real.sin (k*x)*k
  have scale (x : ℝ) : HasDerivAt (fun t : ℝ => k*t) k x := by simpa only [mul_one] using (hasDerivAt_id' x).const_mul k
  have dw (x : ℝ) : HasDerivAt w (u x) x := (Real.hasDerivAt_cos _).comp x (scale x)
  have du (x : ℝ) : HasDerivAt u (-(k^2*w x)) x := by
    convert (((Real.hasDerivAt_sin _).comp x (scale x)).neg.mul_const k) using 1
    dsimp [w]
    ring
  apply interval_energy_of_positive_jacobi_solution (w:=w) (u:=u) (V:=fun _ => k^2)
    (by linarith) smooth (continuous_iff_continuousAt.mpr fun x => (dw x).continuousAt)
    (continuous_iff_continuousAt.mpr fun x => (du x).continuousAt) continuous_const
    (fun x _ => dw x) (fun x _ => du x) _ left right
  intro x hx
  have kb : k*(R+1)=1 := by dsimp [k]; field_simp [(by linarith : R+1≠0)]
  exact Real.cos_pos_of_mem_Ioo ⟨by nlinarith [mul_le_mul_of_nonneg_left hx.1 kp.le,Real.pi_gt_three],
    by nlinarith [mul_le_mul_of_nonneg_left hx.2 kp.le,Real.pi_gt_three]⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.interval_energy_of_positive_jacobi_solution
#print axioms TwoAxisHelicoid.half_helicoid_transverse_interval_nonnegative
#print axioms TwoAxisHelicoid.half_helicoid_axial_interval_gap
