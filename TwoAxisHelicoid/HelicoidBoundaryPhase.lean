import TwoAxisHelicoid.RhombicAxisRelativeDirection
import TwoAxisHelicoid.HelicoidBoundaryCrossing

namespace TwoAxisHelicoid
open Set Filter Topology Complex
open scoped Topology

private theorem rotated_phase_im (k θ r : ℝ) :
    (exp (-(k:ℂ)*I)*((r:ℂ)*exp ((θ:ℂ)*I))).im=r*Real.sin (θ-k) := by
  have e : exp (-(k:ℂ)*I)*exp ((θ:ℂ)*I)=exp (((θ-k:ℝ):ℂ)*I) := by
    rw [← Complex.exp_add]
    push_cast
    ring_nf
  rw [mul_left_comm,e,Complex.mul_im,ofReal_re,ofReal_im,zero_mul,add_zero,exp_ofReal_mul_I_im]

/-- A boundary lift of the actual relative horizontal phase has no
local extremum on the disk side when its limiting direction is the
inward or outward transverse derivative. Both possible signs of the
real proportionality coefficient are admitted. -/
theorem marked_torus_boundary_phase_no_extremum {t : ℝ} (ht : 0<t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hE : IsClosedEmbedding (harmonicTorusImmersion hX)) (α b : ℝ) {n : ℤ} {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) (hx : z.re=n)
    {S : Set ℂ} (disks : HasInwardTangentDisksAt S z) {r F : ℂ → ℝ} (cf : ContinuousWithinAt F S z)
    (polar : ∀ᶠ w in 𝓝[S] z, 0≤r w ∧ helicoidRelativeHorizontal α b (X w)=(r w:ℂ)*exp ((F w:ℂ)*I))
    (limit : ∃ a : ℝ, fderiv ℝ (fun w => helicoidRelativeHorizontal α b (X w)) z 1=(a:ℂ)*exp ((F z:ℂ)*I)) :
    ¬ IsLocalExtrOn F S z := by
  let P := fun w => helicoidRelativeHorizontal α b (X w)
  let k := F z
  let g := helicoidPhaseNormal k
  let T := fun w => axisHelicoidSide g α b (X w)
  have data := rhombic_axis_relative_direction ht hX hE.injective α b hz hx
  have aP : AnalyticAt ℝ P z := data.1
  have eT : T=(fun w => (exp (-(k:ℂ)*I)*P w).im) := funext (fun w => helicoid_side_relative_argument _ _ _ _)
  have on : X z ∈ range (axisRuledHelicoid g α b) := by
    apply (axisHelicoidSide_eq_zero_iff (helicoidPhaseNormal_unit k) α b _).mp
    change T z=0
    rw [eT]
    change (exp (-(k:ℂ)*I)*P z).im=0
    rw [show P z=0 from data.2.1,mul_zero,Complex.zero_im]
  have dT (v : ℂ) : fderiv ℝ T z v=(exp (-(k:ℂ)*I)*fderiv ℝ P z v).im := by
    rw [eT]
    exact congrArg (fun d : ℂ →L[ℝ] ℝ => d v)
      (imCLM.hasFDerivAt.comp z (aP.differentiableAt.hasFDerivAt.const_mul (exp (-(k:ℂ)*I)))).fderiv
  obtain ⟨a,ea⟩ := limit
  have dr : fderiv ℝ T z 1=0 := by
    rw [dT,show fderiv ℝ P z 1=(a:ℂ)*exp ((k:ℂ)*I) from ea,rotated_phase_im,sub_self,Real.sin_zero,mul_zero]
  have di : fderiv ℝ T z I=0 := by rw [dT,show fderiv ℝ P z I=0 from data.2.2.1,mul_zero,Complex.zero_im]
  have flat : fderiv ℝ T z=0 := by
    ext v
    rw [real_linear_complex_expansion (fderiv ℝ T z) v,dr,di,smul_zero,smul_zero,add_zero]
    rfl
  obtain ⟨pos,neg⟩ := marked_torus_crosses_tangent_helicoid_within hX hE (helicoidPhaseNormal_unit k) α b hz disks on flat
  have formula : ∀ᶠ w in 𝓝[S] z, T w=r w*Real.sin (F w-k) := by
    filter_upwards [polar] with w hw
    rw [eT]
    change (exp (-(k:ℂ)*I)*P w).im=_
    rw [show P w=(r w:ℂ)*exp ((F w:ℂ)*I) from hw.2,rotated_phase_im]
  have close : ∀ᶠ w in 𝓝[S] z, |F w-k|<Real.pi := by
    have c : ContinuousWithinAt (fun w => |F w-k|) S z := (cf.sub continuousWithinAt_const).abs
    exact c.tendsto.eventually (gt_mem_nhds (by simp [k,Real.pi_pos]))
  rintro (lo | hi)
  · apply neg
    filter_upwards [lo,polar,formula,close] with w hw p e bound
    change ¬ T w<0
    rw [e]
    exact not_lt_of_ge (mul_nonneg p.1 (Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hw) (abs_lt.mp bound).2.le))
  · apply pos
    filter_upwards [hi,polar,formula,close] with w hw p e bound
    change ¬ 0<T w
    rw [e]
    exact not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos p.1 (Real.sin_nonpos_of_nonpos_of_neg_pi_le (sub_nonpos.mpr hw) (abs_lt.mp bound).1.le))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_torus_boundary_phase_no_extremum
