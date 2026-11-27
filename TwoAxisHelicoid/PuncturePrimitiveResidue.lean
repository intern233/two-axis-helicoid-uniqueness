import TwoAxisHelicoid.ExteriorCirclePrimitive
import TwoAxisHelicoid.AnnularEndInverseEscape

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology Interval

/-- A single logarithmic term removes all monodromy from a holomorphic
differential on the exterior of a circle. This also allows an essential
singularity at infinity. -/
theorem exterior_primitive_modulo_log {f : ℂ → ℂ} {R : ℝ} (hR : 0<R)
    (diff : ∀ w : ℂ, R<‖w‖ → DifferentiableAt ℂ f w) :
    ∃ (c : ℂ) (F : ℂ → ℂ), ∀ w : ℂ, R<‖w‖ → HasDerivAt F (f w-c/w) w := by
  let r := R+1
  have pr : 0<r := by dsimp [r]; linarith
  let x := fun u : ℝ => (r:ℂ)*exp ((u:ℂ)*I)
  have norm (u : ℝ) : ‖x u‖=r := by simp [x,Complex.norm_exp,abs_of_pos pr,Complex.mul_re]
  have nx (u : ℝ) : x u≠0 := norm_pos_iff.mp ((norm u).symm ▸ pr)
  let G := fun u : ℝ => x u*f (x u)
  have cont : Continuous G := by
    have cx : Continuous x := by dsimp [x]; fun_prop
    exact cx.mul (continuous_iff_continuousAt.mpr fun u =>
      (diff (x u) (by rw [norm]; exact lt_add_one _)).continuousAt.comp cx.continuousAt)
  let k : ℂ := (∫ u : ℝ in 0..2*Real.pi, G u)/((2*Real.pi:ℝ):ℂ)
  have kn : ((2*Real.pi:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have period : exteriorAngularPeriod (fun w => f w-k/w) r=0 := by
    have eq (u : ℝ) : x u*(f (x u)-k/x u)=G u-k := by
      rw [mul_sub,mul_div_cancel₀ _ (nx u)]
    change I*(∫ u : ℝ in 0..2*Real.pi, x u*(f (x u)-k/x u))=0
    simp_rw [eq]
    rw [intervalIntegral.integral_sub (cont.intervalIntegrable _ _) intervalIntegrable_const,intervalIntegral.integral_const,
      sub_zero,Complex.real_smul,show ((2*Real.pi:ℝ):ℂ)*k=∫ u : ℝ in 0..2*Real.pi, G u from mul_div_cancel₀ _ kn,
      sub_self,mul_zero]
  obtain ⟨F,d⟩ := exterior_primitive_of_zero_angular_period hR (lt_add_one R) (f := fun w => f w-k/w)
    (fun w hw => (diff w hw).sub ((differentiableAt_const k).div differentiableAt_id (norm_pos_iff.mp (hR.trans hw)))) period
  exact ⟨k,F,d⟩

/-- The corresponding statement at a puncture, with an actual
single-valued holomorphic primitive on the whole punctured disk. -/
theorem puncture_primitive_modulo_log {f : ℂ → ℂ} {r : ℝ} (hr : 0<r)
    (diff : ∀ z : ℂ, 0<‖z‖ → ‖z‖<r → DifferentiableAt ℂ f z) :
    ∃ (c : ℂ) (F : ℂ → ℂ), ∀ z : ℂ, 0<‖z‖ → ‖z‖<r → HasDerivAt F (f z-c/z) z := by
  let R := r⁻¹
  have pos : 0<R := inv_pos.mpr hr
  let q := fun w : ℂ => -((w^2)⁻¹)*f w⁻¹
  have domain (w : ℂ) (hw : R<‖w‖) : 0<‖w⁻¹‖ ∧ ‖w⁻¹‖<r := by
    rw [norm_inv]
    exact ⟨inv_pos.mpr (pos.trans hw),by simpa only [R,inv_inv] using (inv_lt_inv₀ (pos.trans hw) pos).mpr hw⟩
  obtain ⟨c,F,d⟩ := exterior_primitive_modulo_log (f := q) pos (fun w hw =>
    (((differentiableAt_id.pow 2).inv (pow_ne_zero 2 (norm_pos_iff.mp (pos.trans hw)))).neg).mul
      ((diff _ (domain _ hw).1 (domain _ hw).2).comp w (hasDerivAt_inv (norm_pos_iff.mp (pos.trans hw))).differentiableAt))
  refine ⟨-c,fun z => F z⁻¹,?_⟩
  intro z nz small
  have ne := norm_pos_iff.mp nz
  have ext : R<‖z⁻¹‖ := by rw [norm_inv]; exact (inv_lt_inv₀ hr nz).mpr small
  have prod : (q z⁻¹-c/z⁻¹)*(-(z^2)⁻¹)=f z- -c/z := by
    dsimp [q]
    field_simp [ne]
    ring
  simpa only [prod,Function.comp_def] using (d z⁻¹ ext).comp z (hasDerivAt_inv ne)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.puncture_primitive_modulo_log
