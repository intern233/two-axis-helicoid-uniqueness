import TwoAxisHelicoid.SpinCircleAction
import Mathlib.Topology.Homotopy.Lifting

namespace TwoAxisHelicoid
set_option maxHeartbeats 1000000

theorem quaternion_frame_fibers_deck (q r : UnitQuaternion) :
    unitQuaternionFrame q = unitQuaternionFrame r ↔ q = r ∨ q = unitQuaternionAntipode r := by
  rw [unitQuaternionFrame_fibers]
  constructor
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext (h.trans (unitQuaternionAntipode_val r).symm))
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (unitQuaternionAntipode_val r)

theorem phase_endpoint_closes_iff {u v : Circle} {q r : UnitQuaternion}
    (hu : u^2 = v^2) (hq : unitQuaternionFrame q = unitQuaternionFrame r) :
    spinCircleAction u q = spinCircleAction v r ↔ (u = v ↔ q = r) := by
  rcases (circle_square_fibers u v).mp hu with rfl | rfl <;>
    rcases (quaternion_frame_fibers_deck q r).mp hq with rfl | rfl <;>
      simp [spinCircleAction_neg,spinCircleAction_antipode,unitQuaternionAntipode_involutive,
        unitQuaternionAntipode_ne,Circle.neg_ne_self]

/-- A tangent frame rotation around a loop changes the lift sign by the
monodromy of the actual Spin(2) square root of that rotation. -/
theorem rotated_frame_loop_monodromy
    (w : C(unitInterval,Circle)) (hw : w 1 = w 0)
    (q s : C(unitInterval,UnitQuaternion)) (hq : unitQuaternionFrame (q 1) = unitQuaternionFrame (q 0))
    (hs : ∀ r, unitQuaternionFrame (s r) = rotateTangentPair (w r) (unitQuaternionFrame (q r)))
    (u : C(unitInterval,Circle)) (hu : ∀ r, u r^2 = w r) :
    s 1 = s 0 ↔ (u 1 = u 0 ↔ q 1 = q 0) := by
  let a := fun r : unitInterval => spinCircleAction (u r) (q r)
  have hc : Continuous a := spinCircleAction_continuous.comp
    (f := fun r : unitInterval => (u r,q r)) (u.continuous.prodMk q.continuous)
  have he : unitQuaternionFrame ∘ s = unitQuaternionFrame ∘ a := by
    funext r
    change unitQuaternionFrame (s r) = unitQuaternionFrame (spinCircleAction (u r) (q r))
    rw [hs r,unitQuaternionFrame_spinCircleAction,hu r]
  rw [quaternion_frame_lifts_closed_iff s.continuous hc he 0 1]
  exact phase_endpoint_closes_iff ((hu 1).trans (hw.trans (hu 0).symm)) hq

theorem circle_phase_path_half_lift (w : C(unitInterval,Circle)) (u₀ : Circle) (h₀ : u₀^2 = w 0) :
    ∃ u : C(unitInterval,Circle), u 0 = u₀ ∧ ∀ r, u r^2 = w r := by
  let γ : Path (w 0) (w 1) := ⟨w,rfl,rfl⟩
  let cov := circle_square_isCoveringMap
  exact ⟨cov.liftPath γ u₀ h₀.symm,cov.liftPath_zero γ u₀ h₀.symm,
    fun r => congrFun (cov.liftPath_lifts γ u₀ h₀.symm) r⟩

theorem circle_half_angle_closes_iff_even (θ : unitInterval → ℝ) (n : ℤ)
    (h : θ 1-θ 0 = 2*Real.pi*n) :
    Circle.exp (θ 1/2) = Circle.exp (θ 0/2) ↔ Even n := by
  have he : θ 1/2 = ((n : ℝ)*Real.pi)+θ 0/2 := by linarith
  have hπ : Circle.exp Real.pi = -1 := by
    exact Circle.ext (by simp [Circle.coe_exp,Complex.exp_pi_mul_I])
  rw [he,Circle.exp_add,Circle.exp_intCast_mul,hπ]
  rw [mul_eq_right]
  change (-1 : Circle)^n = 1 ↔ Even n
  have hcoe : (-1 : Circle)^n = 1 ↔ (-1 : ℂ)^n = 1 := by
    rw [← Circle.coe_inj]
    simp
  rw [hcoe,neg_one_zpow_eq_ite]
  by_cases hn : Even n <;> norm_num [hn]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rotated_frame_loop_monodromy
#print axioms TwoAxisHelicoid.circle_half_angle_closes_iff_even
