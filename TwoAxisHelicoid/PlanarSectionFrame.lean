import TwoAxisHelicoid.RegularPlanarTurning
import TwoAxisHelicoid.QuaternionTangentStabilizer

namespace TwoAxisHelicoid
open Complex Set
open scoped Quaternion
set_option maxHeartbeats 1000000

def quaternionHorizontalSpinor (q : UnitQuaternion) : ℂ := ⟨q.1.re,q.1.imK⟩

noncomputable def frameHorizontalTangent (q : UnitQuaternion) : ℂ :=
  ⟨(unitQuaternionFrame q).1.1 0,(unitQuaternionFrame q).1.1 1⟩

theorem quaternionHorizontalSpinor_continuous : Continuous quaternionHorizontalSpinor :=
  Complex.equivRealProdCLM.symm.continuous.comp ((Quaternion.continuous_re.comp continuous_subtype_val).prodMk
    (Quaternion.continuous_imK.comp continuous_subtype_val))

theorem quaternionHorizontalSpinor_nonzero (q : UnitQuaternion) (h : (unitQuaternionFrame q).1.2 2 ≠ 0) :
    quaternionHorizontalSpinor q ≠ 0 := by
  intro hz
  have ha := congrArg Complex.re hz
  have hd := congrArg Complex.im hz
  change q.1.re = 0 at ha
  change q.1.imK = 0 at hd
  apply h
  rw [unitQuaternionFrame_axisJ]
  simp [quaternionImaginaryVector,quaternionAxisJ,ha,hd]

theorem quaternionHorizontalSpinor_square (q : UnitQuaternion) (ht : (unitQuaternionFrame q).1.1 2 = 0) :
    quaternionHorizontalSpinor q^2 = frameHorizontalTangent q *
      ((Complex.normSq (quaternionHorizontalSpinor q) : ℝ) : ℂ) := by
  let a := q.1.re
  let b := q.1.imI
  let c := q.1.imJ
  let d := q.1.imK
  have hn : a^2+b^2+c^2+d^2 = 1 := by
    simpa [Quaternion.normSq_def',a,b,c,d,add_assoc] using q.2
  have hz : 2*(b*d-a*c) = 0 := by
    rw [unitQuaternionFrame_axisI] at ht
    simp [quaternionImaginaryVector,quaternionAxisI] at ht
    dsimp only [a,b,c,d]
    linear_combination ht
  apply Complex.ext
  · simp [frameHorizontalTangent,unitQuaternionFrame_axisI,quaternionImaginaryVector,quaternionAxisI,
      quaternionHorizontalSpinor,pow_two,Complex.mul_re,Complex.normSq_apply]
    dsimp only [a,b,c,d] at hn hz
    linear_combination -(q.1.re^2-q.1.imK^2)*hn-(q.1.imI*q.1.imK+q.1.re*q.1.imJ)*hz
  · simp [frameHorizontalTangent,unitQuaternionFrame_axisI,quaternionImaginaryVector,quaternionAxisI,
      quaternionHorizontalSpinor,pow_two,Complex.mul_im,Complex.normSq_apply]
    dsimp only [a,b,c,d] at hn hz
    linear_combination -(2*q.1.re*q.1.imK)*hn+(q.1.re*q.1.imI-q.1.imJ*q.1.imK)*hz

theorem quaternionHorizontalHalfPhase_square (q : UnitQuaternion) (ht : (unitQuaternionFrame q).1.1 2 = 0)
    (hb : (unitQuaternionFrame q).1.2 2 ≠ 0) :
    ((unitComplexDirection (quaternionHorizontalSpinor q) (quaternionHorizontalSpinor_nonzero q hb) : Circle) : ℂ)^2 =
      frameHorizontalTangent q := by
  change ((quaternionHorizontalSpinor q)/(‖quaternionHorizontalSpinor q‖ : ℂ))^2 = _
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero _ (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (quaternionHorizontalSpinor_nonzero q hb))))).mpr
  rw [← ofReal_pow,← normSq_eq_norm_sq]
  exact quaternionHorizontalSpinor_square q ht

/-- On a transverse horizontal plane section of a surface, a closed
quaternion lift of its adapted frame would give a closed half-angle of
its simple planar unit tangent. -/
theorem transverse_planar_section_quaternion_lift_not_closed
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1) (hr : ∀ t, deriv γ t ≠ 0)
    (hi : ∀ t h : ℝ, h ∈ Ioo (0 : ℝ) 1 → γ (t+h) ≠ γ t) (q : C(unitInterval,UnitQuaternion))
    (ht : ∀ t, (unitQuaternionFrame (q t)).1.1 2 = 0)
    (hb : ∀ t, (unitQuaternionFrame (q t)).1.2 2 ≠ 0)
    (hxy : ∀ t : unitInterval, frameHorizontalTangent (q t) = unitComplexDirection (deriv γ t.1) (hr _)) :
    q 1 ≠ q 0 := by
  let u : C(unitInterval,Circle) := ⟨fun t => unitComplexDirection (quaternionHorizontalSpinor (q t))
      (quaternionHorizontalSpinor_nonzero (q t) (hb t)),
    unitComplexDirection_continuous (quaternionHorizontalSpinor_continuous.comp q.continuous) _⟩
  intro he
  apply regular_planar_tangent_no_closed_half_angle hγ hp hr hi u ?_ ?_
  · intro t
    exact Circle.ext ((quaternionHorizontalHalfPhase_square (q t) (ht t) (hb t)).trans (hxy t))
  · apply Circle.ext
    change quaternionHorizontalSpinor (q 1)/(‖quaternionHorizontalSpinor (q 1)‖ : ℂ) =
      quaternionHorizontalSpinor (q 0)/(‖quaternionHorizontalSpinor (q 0)‖ : ℂ)
    rw [he]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.transverse_planar_section_quaternion_lift_not_closed
