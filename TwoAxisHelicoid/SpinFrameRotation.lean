import TwoAxisHelicoid.SpinLiftUniqueness
import Mathlib.Topology.Algebra.ConstMulAction

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 1000000

noncomputable def unitSpinorPhase {u : ℂ} (hu : normSq u = 1) : UnitSpinor ≃ₜ UnitSpinor := by
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu
  exact (Homeomorph.smulOfNeZero u hu0 : (ℂ × ℂ) ≃ₜ (ℂ × ℂ)).subtype (fun s => by
    change spinorWeight s = 1 ↔ spinorWeight (u • s) = 1
    rw [spinorWeight_smul,hu,one_mul])

@[simp] theorem unitSpinorPhase_val {u : ℂ} (hu : normSq u = 1) (s : UnitSpinor) :
    (unitSpinorPhase hu s).1 = u • s.1 := rfl

noncomputable def unitQuaternionPhase {u : ℂ} (hu : normSq u = 1) :
    UnitQuaternion ≃ₜ UnitQuaternion :=
  (unitSpinorQuaternionHomeomorph.symm.trans (unitSpinorPhase hu)).trans
    unitSpinorQuaternionHomeomorph

theorem unitQuaternionPhase_spinor {u : ℂ} (hu : normSq u = 1) (s : UnitSpinor) :
    unitQuaternionPhase hu (unitSpinorQuaternionHomeomorph s) =
      unitSpinorQuaternionHomeomorph (unitSpinorPhase hu s) := by
  change unitSpinorQuaternionHomeomorph
    (unitSpinorPhase hu (unitSpinorQuaternionHomeomorph.symm (unitSpinorQuaternionHomeomorph s))) = _
  rw [unitSpinorQuaternionHomeomorph.symm_apply_apply]

theorem unitQuaternionPhase_antipode {u : ℂ} (hu : normSq u = 1) (q : UnitQuaternion) :
    unitQuaternionPhase hu (unitQuaternionAntipode q) =
      unitQuaternionAntipode (unitQuaternionPhase hu q) := by
  obtain ⟨s,rfl⟩ := unitSpinorQuaternionHomeomorph.surjective q
  rw [unitQuaternionAntipode_spinor,unitQuaternionPhase_spinor,
    unitQuaternionPhase_spinor,unitQuaternionAntipode_spinor]
  apply congrArg unitSpinorQuaternionHomeomorph
  apply Subtype.ext
  change u • (-s.1) = -(u • s.1)
  exact smul_neg _ _

/-- Multiplying the spinor by a fixed unit complex number lifts the
corresponding constant rotation of the tangent frame. -/
theorem unitQuaternionPhase_frame_vectors {u : ℂ} (hu : normSq u = 1) (q : UnitQuaternion) :
    (unitQuaternionFrame (unitQuaternionPhase hu q)).1 =
      ((u^2).re • (unitQuaternionFrame q).1.1+(u^2).im • (unitQuaternionFrame q).1.2,
       -(u^2).im • (unitQuaternionFrame q).1.1+(u^2).re • (unitQuaternionFrame q).1.2) := by
  obtain ⟨s,rfl⟩ := unitSpinorQuaternionHomeomorph.surjective q
  rw [unitQuaternionPhase_spinor,unitQuaternionFrame_spinor,unitQuaternionFrame_spinor]
  change ((fun j => (spinorQuadratic (u • s.1) j).re),
    (fun j => -(spinorQuadratic (u • s.1) j).im)) =
      ((u^2).re • (fun j => (spinorQuadratic s.1 j).re)+
          (u^2).im • (fun j => -(spinorQuadratic s.1 j).im),
       -(u^2).im • (fun j => (spinorQuadratic s.1 j).re)+
          (u^2).re • (fun j => -(spinorQuadratic s.1 j).im))
  rw [spinorQuadratic_smul]
  apply Prod.ext <;> funext j <;> simp [Complex.mul_re,Complex.mul_im]
  ring

/-- A square-root phase aligning a frame with any fixed nonzero complex
direction exists, and has unit norm. -/
theorem exists_unit_direction_half_phase {v : ℂ} (hv : v ≠ 0) :
    ∃ u : ℂ, normSq u = 1 ∧ u^2 = v/(‖v‖ : ℂ) := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hd : normSq (v/(‖v‖ : ℂ)) = 1 := by
    rw [normSq_eq_norm_sq,norm_div,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _),div_self hn,one_pow]
  obtain ⟨u,hu⟩ := complex_has_square_root (v/(‖v‖ : ℂ))
  have hu' : (normSq u)^2 = 1 := by rw [← map_pow,hu,hd]
  refine ⟨u,?_,hu⟩
  nlinarith [normSq_nonneg u]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.unitQuaternionPhase_frame_vectors
#print axioms TwoAxisHelicoid.exists_unit_direction_half_phase
