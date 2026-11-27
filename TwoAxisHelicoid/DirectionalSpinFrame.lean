import TwoAxisHelicoid.SpinFrameRotation

namespace TwoAxisHelicoid
open Complex

theorem real_linear_complex_expansion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : ℂ →L[ℝ] E) (v : ℂ) : D v = v.re • D 1+v.im • D I := by
  have hv : v.re • (1 : ℂ)+v.im • I = v := by
    apply Complex.ext <;> simp [Complex.real_smul]
  calc
    D v = D (v.re • (1 : ℂ)+v.im • I) := congrArg D hv.symm
    _ = _ := by rw [map_add,map_smul,map_smul]

/-- The constant spin phase aligns the first frame vector with the
actual derivative in direction v, and the second with its oriented
quarter-turn Iv. -/
theorem quaternion_phase_aligns_differential
    (D : ℂ →L[ℝ] (Fin 3 → ℝ)) (K : ℝ) (q : UnitQuaternion)
    (hq : (unitQuaternionFrame q).1 = (K • D 1,K • D I))
    {u v : ℂ} (hu : normSq u = 1) (huv : u^2 = v/(‖v‖ : ℂ)) :
    (unitQuaternionFrame (unitQuaternionPhase hu q)).1 =
      ((K/‖v‖) • D v,(K/‖v‖) • D (I*v)) := by
  have hr : (u^2).re = v.re/‖v‖ := by rw [huv]; simp
  have hi : (u^2).im = v.im/‖v‖ := by rw [huv]; simp
  rw [unitQuaternionPhase_frame_vectors,hq,hr,hi,
    real_linear_complex_expansion D v,real_linear_complex_expansion D (I*v)]
  apply Prod.ext <;> funext j <;> simp [Complex.mul_re,Complex.mul_im]
  · ring
  · ring

noncomputable def generatorHalfPhase (L : PeriodPair) (i : Fin 2) : ℂ :=
  (exists_unit_direction_half_phase (L.basis.ne_zero i)).choose

theorem generatorHalfPhase_unit (L : PeriodPair) (i : Fin 2) :
    normSq (generatorHalfPhase L i) = 1 :=
  (exists_unit_direction_half_phase (L.basis.ne_zero i)).choose_spec.1

theorem generatorHalfPhase_square (L : PeriodPair) (i : Fin 2) :
    generatorHalfPhase L i^2 = L.basis i/(‖L.basis i‖ : ℂ) :=
  (exists_unit_direction_half_phase (L.basis.ne_zero i)).choose_spec.2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.quaternion_phase_aligns_differential
#print axioms TwoAxisHelicoid.generatorHalfPhase_square
