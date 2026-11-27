import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Complex Real Set Filter Topology
open scoped Topology ContDiff

noncomputable def contactAngleBase (n : ℕ) (C : ℂ) : ℝ := -C.arg/n
noncomputable def contactArmAngle (n : ℕ) (C : ℂ) (k : ℤ) : ℝ :=
  contactAngleBase n C+((k:ℝ)+1/2)*(Real.pi/n)

/-- The angular profile of the leading harmonic polynomial. -/
theorem contact_circle_real_profile (C : ℂ) (n : ℕ) (θ : ℝ) :
    (C*(circleMap 0 1 θ)^n).re=‖C‖*Real.cos (C.arg+n*θ) := by
  have polar : circleMap 0 ‖C‖ C.arg=C := by
    simpa only [circleMap_zero] using Complex.norm_mul_exp_arg_mul_I C
  calc
    _=(circleMap 0 ‖C‖ C.arg*(circleMap 0 1 θ)^n).re := by rw [polar]
    _=_ := by rw [circleMap_zero_pow,circleMap_zero_mul,circleMap_zero_re,one_pow,mul_one]

private theorem contact_phase {n : ℕ} (hn : 0<n) (C : ℂ) (k : ℤ) :
    C.arg+(n:ℝ)*contactArmAngle n C k=(2*(k:ℝ)+1)*Real.pi/2 := by
  have ne : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  dsimp [contactArmAngle,contactAngleBase]
  field_simp
  ring

theorem contact_circle_zero_iff {C : ℂ} (nz : C≠0) {n : ℕ} (hn : 0<n) {θ : ℝ} :
    (C*(circleMap 0 1 θ)^n).re=0 ↔ ∃ k : ℤ, θ=contactArmAngle n C k := by
  rw [contact_circle_real_profile,mul_eq_zero,or_iff_right (norm_ne_zero_iff.mpr nz),Real.cos_eq_zero_iff]
  constructor
  · rintro ⟨k,h⟩
    exact ⟨k,mul_left_cancel₀ (by exact_mod_cast hn.ne' : (n:ℝ)≠0)
      (add_left_cancel (h.trans (contact_phase hn C k).symm))⟩
  · rintro ⟨k,rfl⟩
    exact ⟨k,contact_phase hn C k⟩

/-- Each of the zero directions has a nonvanishing angular derivative. -/
theorem contact_circle_zero_transverse {C : ℂ} (nz : C≠0) {n : ℕ} (hn : 0<n) {θ : ℝ}
    (atZero : (C*(circleMap 0 1 θ)^n).re=0) :
    deriv (fun t : ℝ => (C*(circleMap 0 1 t)^n).re) θ≠0 := by
  have np : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have cp := (mul_eq_zero.mp ((contact_circle_real_profile C n θ).symm.trans atZero)).resolve_left (norm_ne_zero_iff.mpr nz)
  have sn : Real.sin (C.arg+n*θ)≠0 := by
    intro h
    have same := Real.sin_sq_add_cos_sq (C.arg+n*θ)
    rw [h,cp] at same
    norm_num at same
  have d := (((Real.hasDerivAt_cos (C.arg+n*θ)).comp θ
    (((hasDerivAt_id θ).const_mul (n:ℝ)).const_add C.arg)).const_mul ‖C‖).deriv
  rw [funext (contact_circle_real_profile C n)]
  exact d ▸ mul_ne_zero (norm_ne_zero_iff.mpr nz) (mul_ne_zero (neg_ne_zero.mpr sn) (mul_ne_zero np one_ne_zero))

theorem contact_arm_angle_strict {n : ℕ} (hn : 0<n) (C : ℂ) : StrictMono (contactArmAngle n C) := by
  intro i j h
  apply add_lt_add_right
  apply mul_lt_mul_of_pos_right _ (div_pos Real.pi_pos (by exact_mod_cast hn))
  exact add_lt_add_left (by exact_mod_cast h) _

private theorem contact_angle_width {n : ℕ} (hn : 0<n) :
    (2*(n:ℝ))*(Real.pi/n)=2*Real.pi := by field_simp [show (n:ℝ)≠0 by exact_mod_cast hn.ne']

theorem contact_arm_inside_period {n : ℕ} (hn : 0<n) (C : ℂ) (i : Fin (2*n)) :
    contactArmAngle n C i.1∈Ioo (contactAngleBase n C) (contactAngleBase n C+2*Real.pi) := by
  let δ := Real.pi/n
  have dp : 0<δ := div_pos Real.pi_pos (by exact_mod_cast hn)
  have upper : (i.1:ℝ)+1/2<2*(n:ℝ) := by
    have le : i.1+1≤2*n := i.isLt
    have cast : (i.1:ℝ)+1≤2*(n:ℝ) := by exact_mod_cast le
    linarith
  change _<contactAngleBase n C+((i.1:ℝ)+1/2)*δ ∧ _<_
  refine ⟨lt_add_of_pos_right _ (mul_pos (by positivity) dp),?_⟩
  exact add_lt_add_right ((mul_lt_mul_of_pos_right upper dp).trans_eq (contact_angle_width hn)) _

/-- One full angle interval, with nonzero profile at both ends, contains
exactly the specified 2n zeros. They are separated by π/n. -/
theorem contact_zeros_in_period {C : ℂ} (nz : C≠0) {n : ℕ} (hn : 0<n) {θ : ℝ}
    (inside : θ∈Icc (contactAngleBase n C) (contactAngleBase n C+2*Real.pi)) :
    (C*(circleMap 0 1 θ)^n).re=0 ↔ ∃ i : Fin (2*n), θ=contactArmAngle n C i.1 := by
  rw [contact_circle_zero_iff nz hn]
  refine ⟨?_,fun ⟨i,h⟩ => ⟨i.1,h⟩⟩
  rintro ⟨k,rfl⟩
  let δ := Real.pi/n
  have dp : 0<δ := div_pos Real.pi_pos (by exact_mod_cast hn)
  have low : 0≤((k:ℝ)+1/2)*δ := by
    have h := inside.1
    change contactAngleBase n C≤contactAngleBase n C+((k:ℝ)+1/2)*δ at h
    linarith
  have high : ((k:ℝ)+1/2)*δ≤(2*(n:ℝ))*δ := by
    rw [show (2*(n:ℝ))*δ=2*Real.pi from contact_angle_width hn]
    exact le_of_add_le_add_left inside.2
  have kn : 0≤k := by
    by_contra! neg
    have le : (k:ℝ)≤ -1 := by exact_mod_cast (show k≤ -1 by omega)
    exact low.not_gt (mul_neg_of_neg_of_pos (by linarith) dp)
  have ku : k<(2*n:ℕ) := by
    by_contra! large
    have le : 2*(n:ℝ)≤(k:ℝ) := by exact_mod_cast large
    exact high.not_gt (mul_lt_mul_of_pos_right (by linarith) dp)
  let i : Fin (2*n) := ⟨k.toNat,by omega⟩
  exact ⟨i,congrArg (contactArmAngle n C) (Int.toNat_of_nonneg kn).symm⟩

/-- After all 2n physical tangent directions, the angular parameter
returns to the same unit tangent. -/
theorem contact_direction_full_turn {n : ℕ} (pos : 0<n) (C : ℂ) (k : ℤ) :
    circleMap 0 1 (contactArmAngle n C (k+2*(n:ℤ)))=circleMap 0 1 (contactArmAngle n C k) := by
  have width : contactArmAngle n C (k+2*(n:ℤ))=contactArmAngle n C k+2*Real.pi := by
    simp only [contactArmAngle,Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
    have h := contact_angle_width pos
    linear_combination h
  rw [width,periodic_circleMap]
  
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.contact_zeros_in_period
#print axioms TwoAxisHelicoid.contact_circle_zero_transverse
