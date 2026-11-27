import TwoAxisHelicoid.SpinGeneratorHolonomy

namespace TwoAxisHelicoid
open Set

theorem unitQuaternionAntipode_involutive (q : UnitQuaternion) :
    unitQuaternionAntipode (unitQuaternionAntipode q) = q := by
  apply Subtype.ext
  rw [unitQuaternionAntipode_val,unitQuaternionAntipode_val,neg_neg]

theorem unitQuaternionAntipode_ne (q : UnitQuaternion) : unitQuaternionAntipode q ≠ q := by
  obtain ⟨s,rfl⟩ := unitSpinorQuaternionHomeomorph.surjective q
  rw [unitQuaternionAntipode_spinor]
  exact fun h => unitSpinorAntipode_ne s (unitSpinorQuaternionHomeomorph.injective h)

/-- Any two continuous quaternion lifts of the same oriented frame on a
connected parameter space differ by one constant deck transformation. -/
theorem quaternion_frame_lifts_equal_or_antipodal
    {A : Type*} [TopologicalSpace A] [PreconnectedSpace A] {q r : A → UnitQuaternion}
    (hq : Continuous q) (hr : Continuous r)
    (he : unitQuaternionFrame ∘ q = unitQuaternionFrame ∘ r) (a : A) :
    q = r ∨ q = unitQuaternionAntipode ∘ r := by
  have ha := congrFun he a
  rcases unitQuaternionFrame_fibers.mp ha with ha | ha
  · exact Or.inl (unitQuaternionFrame_isCoveringMap.eq_of_comp_eq hq hr he a (Subtype.ext ha))
  · right
    have he' : unitQuaternionFrame ∘ q = unitQuaternionFrame ∘ (unitQuaternionAntipode ∘ r) := by
      funext x
      exact (congrFun he x).trans (unitQuaternionFrame_antipode (r x)).symm
    have ha' : q a = unitQuaternionAntipode (r a) := by
      apply Subtype.ext
      rw [unitQuaternionAntipode_val]
      exact ha
    exact unitQuaternionFrame_isCoveringMap.eq_of_comp_eq hq
      (unitQuaternionAntipode.continuous.comp hr) he' a ha'

/-- Closure of a lift is intrinsic, independent of either choice of its
initial point in the two-element quaternion fiber. -/
theorem quaternion_frame_lifts_closed_iff
    {A : Type*} [TopologicalSpace A] [PreconnectedSpace A] {q r : A → UnitQuaternion}
    (hq : Continuous q) (hr : Continuous r)
    (he : unitQuaternionFrame ∘ q = unitQuaternionFrame ∘ r) (a b : A) :
    q b = q a ↔ r b = r a := by
  rcases quaternion_frame_lifts_equal_or_antipodal hq hr he a with rfl | rfl
  · rfl
  · exact unitQuaternionAntipode.injective.eq_iff

/-- For the actual second generator, every continuous lift is closed
exactly when the integer branch is even. -/
theorem weierstrass_second_generator_any_lift_closed_iff
    {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1)
    (m : ℤ) {C : ℂ} (hC : C ≠ 0) {q : unitInterval → UnitQuaternion}
    (hq : Continuous q)
    (hframe : ∀ s, unitQuaternionFrame (q s) =
      weierstrassTorusFrame ht ha m hC (puncturedTorusGeneratorLoop _ 1 s)) :
    q 1 = q 0 ↔ Even m := by
  let r : unitInterval → UnitQuaternion := fun s => weierstrassGeneratorLift ht ha m hC 1 s
  have hr : Continuous r := (weierstrassGeneratorLift_continuous ht ha m hC 1).comp continuous_subtype_val
  have he : unitQuaternionFrame ∘ q = unitQuaternionFrame ∘ r := by
    funext s
    exact (hframe s).trans (weierstrassGeneratorLift_frame ht ha m hC 1 s).symm
  rw [quaternion_frame_lifts_closed_iff hq hr he 0 1]
  change weierstrassGeneratorLift ht ha m hC 1 1 =
    weierstrassGeneratorLift ht ha m hC 1 0 ↔ Even m
  rw [(weierstrassGeneratorLift_endpoints ht ha m hC).2]
  by_cases hm : Even m
  · simp only [hm,ite_true,iff_self]
  · simp only [hm,ite_false,unitQuaternionAntipode_ne,iff_self]

theorem weierstrass_first_generator_any_lift_closed
    {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1)
    (m : ℤ) {C : ℂ} (hC : C ≠ 0) {q : unitInterval → UnitQuaternion}
    (hq : Continuous q)
    (hframe : ∀ s, unitQuaternionFrame (q s) =
      weierstrassTorusFrame ht ha m hC (puncturedTorusGeneratorLoop _ 0 s)) :
    q 1 = q 0 := by
  let r : unitInterval → UnitQuaternion := fun s => weierstrassGeneratorLift ht ha m hC 0 s
  have hr : Continuous r := (weierstrassGeneratorLift_continuous ht ha m hC 0).comp continuous_subtype_val
  have he : unitQuaternionFrame ∘ q = unitQuaternionFrame ∘ r := by
    funext s
    exact (hframe s).trans (weierstrassGeneratorLift_frame ht ha m hC 0 s).symm
  exact (quaternion_frame_lifts_closed_iff hq hr he 0 1).mpr
    (weierstrassGeneratorLift_endpoints ht ha m hC).1

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.quaternion_frame_lifts_equal_or_antipodal
#print axioms TwoAxisHelicoid.weierstrass_second_generator_any_lift_closed_iff
