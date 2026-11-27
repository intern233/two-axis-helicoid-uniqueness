import TwoAxisHelicoid.GenusOneSpinQuadratic
import TwoAxisHelicoid.SpinCircleAction

namespace TwoAxisHelicoid
open Complex Set
set_option maxHeartbeats 1000000

/-- Along any puncture-avoiding plane path with lattice endpoint
displacement, a fixed tangent-adapting phase leaves the endpoint
monodromy unchanged. -/
theorem constant_phase_path_lift_closes_iff (L : PeriodPair)
    (χ : L.lattice →+ ZMod 2) (s : PuncturedLatticePlane L → UnitSpinor)
    (hs : UnitSpinorEquivariant L χ s) (hscont : Continuous s)
    (γ : C(unitInterval,PuncturedLatticePlane L)) (ω : L.lattice)
    (hends : (γ 1).1 = (γ 0).1+ω.1) (u : Circle)
    (q : C(unitInterval,UnitQuaternion))
    (hq : ∀ r, unitQuaternionFrame (q r) =
      unitQuaternionFrame (spinCircleAction u (unitSpinorQuaternionHomeomorph (s (γ r))))) :
    q 1 = q 0 ↔ χ ω = 0 := by
  let f := fun r : unitInterval => spinCircleAction u (unitSpinorQuaternionHomeomorph (s (γ r)))
  have hf : Continuous f :=
    spinCircleAction_continuous.comp
      (f := fun r : unitInterval => (u,unitSpinorQuaternionHomeomorph (s (γ r)))) (continuous_const.prodMk
      (unitSpinorQuaternionHomeomorph.continuous.comp (hscont.comp γ.continuous)))
  have he : unitQuaternionFrame ∘ q = unitQuaternionFrame ∘ f := funext hq
  refine (quaternion_frame_lifts_closed_iff (q := q) (r := f) q.continuous hf he 0 1).trans ?_
  change spinCircleAction u (unitSpinorQuaternionHomeomorph (s (γ 1))) =
    spinCircleAction u (unitSpinorQuaternionHomeomorph (s (γ 0))) ↔ _
  rw [hs ω (γ 0) (γ 1) hends]
  rcases zmod_two_cases (χ ω) with h | h
  · simp [h]
  · rw [h,unitSpinor_vadd_one,← unitQuaternionAntipode_spinor,spinCircleAction_antipode]
    simp [unitQuaternionAntipode_ne]

/-- For a nonzero mod-two displacement the explicit quadratic refinement
equals one plus the sign character, exactly the bit read by closed lift. -/
theorem integerGeneratorQuadratic_eq_character (m : ℤ) (x : ZMod 2 × ZMod 2) (hx : x ≠ 0) :
    integerGeneratorQuadratic m x = 1+(m : ZMod 2)*x.2 := by
  rcases x with ⟨a,b⟩
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · exact False.elim (hx rfl)
  · simp [integerGeneratorQuadratic,torusQuadratic]
  · simp [integerGeneratorQuadratic,torusQuadratic]
  · change 1*1+(1+(m : ZMod 2))*1+1*1 = 1+(m : ZMod 2)*1
    rcases zmod_two_cases (m : ZMod 2) with h | h <;> rw [h] <;> decide

noncomputable def latticeClassModTwo (L : PeriodPair) (ω : L.lattice) : ZMod 2 × ZMod 2 :=
  ((L.latticeEquivProd ω).1,(L.latticeEquivProd ω).2)

/-- All paths with any nonzero mod-two endpoint displacement, including
the diagonal class, recover the quadratic value from the actual ambient
quaternion cover. The constant phase may align the frame with any fixed
straight-line direction. -/
theorem integer_frame_path_lift_closes_iff_quadratic
    {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) {C : ℂ} (hC : C ≠ 0)
    (γ : C(unitInterval,PuncturedLatticePlane (rhombicPeriodPair t ht)))
    (ω : (rhombicPeriodPair t ht).lattice) (hends : (γ 1).1 = (γ 0).1+ω.1)
    (u : Circle) (q : C(unitInterval,UnitQuaternion))
    (hq : ∀ r, unitQuaternionFrame (q r) =
      unitQuaternionFrame (spinCircleAction u (unitSpinorQuaternionHomeomorph
        (weierstrassUnitLift ht ha m hC (γ r)))))
    (hn : latticeClassModTwo (rhombicPeriodPair t ht) ω ≠ 0) :
    q 1 = q 0 ↔ integerGeneratorQuadratic m (latticeClassModTwo (rhombicPeriodPair t ht) ω) = 1 := by
  rw [constant_phase_path_lift_closes_iff _ _ _ (weierstrassUnitLift_equivariant ht ha m hC)
    (weierstrassUnitLift_continuous ht ha m hC) γ ω hends u q hq,
    integerGeneratorQuadratic_eq_character _ _ hn]
  change ((m*((rhombicPeriodPair t ht).latticeEquivProd ω).2 : ℤ) : ZMod 2) = 0 ↔ _
  rw [Int.cast_mul]
  simp [latticeClassModTwo]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.integer_frame_path_lift_closes_iff_quadratic
