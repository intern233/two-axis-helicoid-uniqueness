import TwoAxisHelicoid.ExteriorCirclePrimitive
import TwoAxisHelicoid.AnnularEndInverseEscape

namespace TwoAxisHelicoid
open Complex Real Set Filter MeasureTheory Metric
open scoped Topology Interval

private theorem exterior_even_angular_period {f : ℂ → ℂ} {r : ℝ} (hr : 0<r)
    (cont : ∀ z : ℂ, ‖z‖=r → ContinuousAt f z) (even : ∀ z : ℂ, ‖z‖=r → f (-z)=f z) :
    exteriorAngularPeriod f r=0 := by
  let c := circleMap (0:ℂ) r
  let F := fun θ => c θ*f (c θ)
  have rad (θ : ℝ) : ‖c θ‖=r := (norm_circleMap_zero r θ).trans (abs_of_pos hr)
  have cc : Continuous c := continuous_circleMap 0 r
  have cf : Continuous F := cc.mul (continuous_iff_continuousAt.mpr
    (fun θ => (cont (c θ) (rad θ)).comp cc.continuousAt))
  have shift (θ : ℝ) : c (θ+π)= -c θ := by simp [c,circleMap,ofReal_add,add_mul,Complex.exp_add,Complex.exp_pi_mul_I]
  have half (θ : ℝ) : F (θ+π)= -F θ := by dsimp [F]; rw [shift,even _ (rad _)]; ring
  have add := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (cf.intervalIntegrable 0 π) (cf.intervalIntegrable π (2*π))
  have off := intervalIntegral.integral_comp_add_right (f := F) (a := 0) (b := π) π
  simp only [half,intervalIntegral.integral_neg,zero_add,← two_mul] at off
  rw [← off,add_neg_cancel] at add
  have rep : exteriorAngularPeriod f r=I*(∫ θ in (0:ℝ)..2*π,F θ) := by
    simp only [exteriorAngularPeriod,F,c,circleMap_zero]
  rw [rep,← add,mul_zero]

/-- Every even holomorphic coefficient on a punctured disk has a
single-valued primitive there, regardless of its singularity. The
odd half-period of the true angular integrand cancels exactly. -/
theorem even_punctured_primitive {f : ℂ → ℂ} {r : ℝ} (hr : 0<r)
    (diff : ∀ z : ℂ, 0<‖z‖ → ‖z‖<r → DifferentiableAt ℂ f z)
    (even : ∀ z : ℂ, 0<‖z‖ → ‖z‖<r → f (-z)=f z) :
    ∃ H : ℂ → ℂ, ∀ z : ℂ, 0<‖z‖ → ‖z‖<r → HasDerivAt H (f z) z := by
  let R := r⁻¹
  have pos : 0<R := inv_pos.mpr hr
  let q := fun w : ℂ => -((w^2)⁻¹)*f w⁻¹
  have domain (w : ℂ) (hw : R<‖w‖) : 0<‖w⁻¹‖ ∧ ‖w⁻¹‖<r := by
    rw [norm_inv]
    refine ⟨inv_pos.mpr (pos.trans hw),?_⟩
    simpa only [R,inv_inv] using (inv_lt_inv₀ (pos.trans hw) pos).mpr hw
  have dq (w : ℂ) (hw : R<‖w‖) : DifferentiableAt ℂ q w := by
    have nw := norm_pos_iff.mp (pos.trans hw)
    exact (((differentiableAt_id.pow 2).inv (pow_ne_zero 2 nw)).neg).mul
      ((diff w⁻¹ (domain w hw).1 (domain w hw).2).comp w (hasDerivAt_inv nw).differentiableAt)
  have eq (w : ℂ) (hw : R<‖w‖) : q (-w)=q w := by
    simp only [q,neg_sq,inv_neg,even w⁻¹ (domain w hw).1 (domain w hw).2]
  have period := exterior_even_angular_period (r := R+1) (by linarith)
    (fun w hw => (dq w (by rw [hw]; linarith)).continuousAt) (fun w hw => eq w (by rw [hw]; linarith))
  obtain ⟨F,dF⟩ := exterior_primitive_of_zero_angular_period pos (lt_add_one R) dq period
  refine ⟨fun z => F z⁻¹,?_⟩
  intro z nz small
  have ne := norm_pos_iff.mp nz
  have ext : R<‖z⁻¹‖ := by rw [norm_inv]; exact (inv_lt_inv₀ hr nz).mpr small
  have h := (dF z⁻¹ ext).comp z (hasDerivAt_inv ne)
  have product : q z⁻¹*(-(z^2)⁻¹)=f z := by
    dsimp [q]
    field_simp [ne]
  simpa only [product,Function.comp_def] using h

/-- An even logarithmic derivative has zero puncture monodromy. Thus a
nonvanishing analytic map with this symmetry has an actual analytic
logarithm on a whole punctured neighborhood. -/
theorem punctured_log_of_even_log_derivative {g : ℂ → ℂ} {r : ℝ} (hr : 0<r)
    (reg : ∀ z : ℂ, 0<‖z‖ → ‖z‖<r → AnalyticAt ℂ g z ∧ g z≠0)
    (even : ∀ z : ℂ, 0<‖z‖ → ‖z‖<r → logDeriv g (-z)=logDeriv g z) :
    ∃ H : ℂ → ℂ, ∀ z : ℂ, 0<‖z‖ → ‖z‖<r → HasDerivAt H (logDeriv g z) z ∧ exp (H z)=g z := by
  have diff (z : ℂ) (nz : 0<‖z‖) (small : ‖z‖<r) : DifferentiableAt ℂ (logDeriv g) z :=
    ((reg z nz small).1.deriv.div (reg z nz small).1 (reg z nz small).2).differentiableAt
  obtain ⟨A,dA⟩ := even_punctured_primitive hr diff even
  let V := {z : ℂ | 0<‖z‖ ∧ ‖z‖<r}
  let f := fun z => g z*exp (-A z)
  have op : IsOpen V := (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have d (z : ℂ) (hz : z∈V) : HasDerivAt f 0 z := by
    have h := ((reg z hz.1 hz.2).1.differentiableAt.hasDerivAt).mul (dA z hz.1 hz.2).neg.cexp
    convert h using 1
    rw [logDeriv_apply]
    field_simp [(reg z hz.1 hz.2).2]
    ring
  let b : ℂ := r/2
  have vb : b∈V := by
    have n : ‖b‖=r/2 := by simp [b,abs_of_pos hr]
    exact ⟨n ▸ half_pos hr,n ▸ half_lt_self hr⟩
  have const (z : ℂ) (hz : z∈V) : f z=f b := by
    apply op.is_const_of_deriv_eq_zero (𝕜 := ℂ) (complex_open_annulus_isPreconnected (r := 0) (R := r) le_rfl)
      (fun w hw => (d w hw).differentiableAt.differentiableWithinAt) (fun w hw => (d w hw).deriv) hz vb
  have nb : f b≠0 := mul_ne_zero (reg b vb.1 vb.2).2 (exp_ne_zero _)
  refine ⟨fun z => A z+log (f b),?_⟩
  intro z nz small
  refine ⟨(dA z nz small).add_const _,?_⟩
  change Complex.exp (A z+Complex.log (f b))=g z
  rw [Complex.exp_add,Complex.exp_log nb,← const z ⟨nz,small⟩]
  simp [f,Complex.exp_neg,Complex.exp_ne_zero,mul_left_comm]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.even_punctured_primitive
#print axioms TwoAxisHelicoid.punctured_log_of_even_log_derivative
