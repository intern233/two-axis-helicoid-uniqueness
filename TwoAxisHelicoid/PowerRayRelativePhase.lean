import TwoAxisHelicoid.ExponentialPowerRay
import TwoAxisHelicoid.HelicoidSectorPhaseRigidity

namespace TwoAxisHelicoid
open Complex Filter
open scoped Topology ComplexConjugate

/-- The square of the unit direction of a nonzero complex number,
which assigns the same value to either orientation of a real line. -/
noncomputable def complexLinePhase (z : ℂ) := z/conj z

theorem complexLinePhase_mul (z w : ℂ) :
    complexLinePhase (z*w)=complexLinePhase z*complexLinePhase w := by
  simp only [complexLinePhase,map_mul]
  ring

theorem complexLinePhase_exp (z : ℂ) :
    complexLinePhase (exp z)=exp (((2*z.im:ℝ):ℂ)*I) := by
  rw [complexLinePhase,← exp_conj,← exp_sub]
  congr 1
  apply Complex.ext <;> simp; ring

theorem exponentialPowerRay_phase (m : ℤ) (μ : ℂ) {t : ℝ} (pos : 0<t) :
    complexLinePhase (exponentialPowerRay m μ t)=exp (((2*μ.im*t:ℝ):ℂ)*I) := by
  have nz : ((t^m:ℝ):ℂ)≠0 := ofReal_ne_zero.mpr (zpow_ne_zero _ pos.ne')
  rw [exponentialPowerRay,complexLinePhase_mul,complexLinePhase_exp]
  simp only [complexLinePhase,conj_ofReal,div_self nz,one_mul,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add,mul_assoc]

/-- A horizontal position asymptotic to a nonzero multiple of an
exponential power and asymptotic to a rotating real line has exactly
that angular speed. The limiting coefficient belongs to the real line. -/
theorem relative_height_phase_forces_ray_limit (m : ℤ) (μ : ℂ) (v : ℝ) {Z : ℝ → ℂ} {q : ℂ} (nq : q≠0)
    (growth : Tendsto (fun t => Z t/exponentialPowerRay m μ t) atTop (𝓝 q))
    (position : Tendsto (fun t : ℝ => complexLinePhase (exp (((-(v*t):ℝ):ℂ)*I)*Z t)) atTop (𝓝 1)) :
    μ.im=v ∧ q.im=0 := by
  let U := exponentialPowerRay m μ
  let P := fun t => complexLinePhase (Z t/U t)
  let C := complexLinePhase q
  have nC : C≠0 := div_ne_zero nq ((map_ne_zero _).mpr nq)
  have angle : Tendsto P atTop (𝓝 C) := growth.div (continuous_conj.continuousAt.tendsto.comp growth) ((map_ne_zero _).mpr nq)
  have osc : Tendsto (fun t : ℝ => C*exp (((2*(μ.im-v)*t:ℝ):ℂ)*I)) atTop (𝓝 1) := by
    have compare := ((tendsto_const_nhds (x := C)).div angle nC).mul position
    rw [div_self nC,one_mul] at compare
    apply compare.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ),angle.eventually_ne nC] with t ht np
    have uN : U t≠0 := mul_ne_zero (ofReal_ne_zero.mpr (zpow_ne_zero _ ht.ne')) (exp_ne_zero _)
    have z : Z t=(Z t/U t)*U t := (div_mul_cancel₀ _ uN).symm
    have zP : complexLinePhase (Z t)=P t*complexLinePhase (U t) := by
      conv_lhs => rw [z,complexLinePhase_mul]
    rw [complexLinePhase_mul,zP,complexLinePhase_exp,exponentialPowerRay_phase m μ ht]
    have e : exp (((2*((((-(v*t):ℝ):ℂ)*I).im):ℝ):ℂ)*I)*exp (((2*μ.im*t:ℝ):ℂ)*I)=exp (((2*(μ.im-v)*t:ℝ):ℂ)*I) := by
      rw [← exp_add]
      congr 1
      rw [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,I_im,I_re,mul_one,zero_mul,add_zero]
      push_cast
      ring
    rw [← e]
    change (C/P t)*(_*(P t*_))=C*(_*_)
    field_simp [np]
  obtain ⟨speed,constant⟩ := constant_phase_of_limit osc
  have real' : q=conj q := (div_eq_one_iff_eq ((map_ne_zero _).mpr nq)).mp constant
  have im := congrArg Complex.im real'
  rw [conj_im] at im
  exact ⟨by linarith,by linarith⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.relative_height_phase_forces_ray_limit
