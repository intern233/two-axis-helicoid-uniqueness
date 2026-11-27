import TwoAxisHelicoid.DirectionalSpinFrame
import TwoAxisHelicoid.CapGeneratorFrame

namespace TwoAxisHelicoid
open Complex Set

/-- The explicit lift after the constant rotation aligning its frame
with the actual lattice-generator tangent direction. -/
noncomputable def adaptedWeierstrassGeneratorLift {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) {C : ℂ} (hC : C ≠ 0) (i : Fin 2) :
    ℝ → UnitQuaternion :=
  unitQuaternionPhase (generatorHalfPhase_unit (rhombicPeriodPair t ht) i) ∘
    weierstrassGeneratorLift ht ha m hC i

theorem adaptedWeierstrassGeneratorLift_continuous {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) {C : ℂ} (hC : C ≠ 0) (i : Fin 2) :
    Continuous (adaptedWeierstrassGeneratorLift ht ha m hC i) :=
  (unitQuaternionPhase (generatorHalfPhase_unit _ i)).continuous.comp
    (weierstrassGeneratorLift_continuous ht ha m hC i)

theorem adaptedWeierstrassGeneratorLift_endpoints {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) {C : ℂ} (hC : C ≠ 0) :
    adaptedWeierstrassGeneratorLift ht ha m hC 0 1 =
      adaptedWeierstrassGeneratorLift ht ha m hC 0 0 ∧
    adaptedWeierstrassGeneratorLift ht ha m hC 1 1 =
      if Even m then adaptedWeierstrassGeneratorLift ht ha m hC 1 0
      else unitQuaternionAntipode (adaptedWeierstrassGeneratorLift ht ha m hC 1 0) := by
  obtain ⟨h0,h1⟩ := weierstrassGeneratorLift_endpoints ht ha m hC
  constructor
  · exact congrArg (unitQuaternionPhase (generatorHalfPhase_unit _ 0)) h0
  · dsimp only [adaptedWeierstrassGeneratorLift,Function.comp_apply]
    rw [h1]
    by_cases hm : Even m
    · simp only [hm,ite_true]
    · simp only [hm,ite_false,unitQuaternionPhase_antipode]

/-- The rotated spin lift is a tangent-adapted frame of the actual cap.
Both vectors are normalized actual derivatives, along v and Iv. -/
theorem harmonic_integer_cap_adapted_generator_frame
    {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (m : ℤ) {C : ℂ} (hC0 : C ≠ 0) (hC : C^2 = (c : ℂ)/(2*thetaSigma t a^2))
    {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hp : ∀ z ω₀, ω₀ ∈ (rhombicPeriodPair t ht).lattice → X (z+ω₀) = X z)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z)
    {F : PeriodTorus (rhombicPeriodPair t ht) → Fin 3 → ℝ}
    {U : Set (PeriodTorus (rhombicPeriodPair t ht))} (hU : IsOpen U)
    (hfix : ∀ q ∈ U, F q = periodTorusLift (rhombicPeriodPair t ht) X hp q)
    (hcore : Subtype.val '' puncturedGeneratorCore (rhombicPeriodPair t ht) ⊆ U)
    (i : Fin 2) (s : unitInterval) :
    let L := rhombicPeriodPair t ht
    let z := periodBasisLine L i s
    let K := (spinorWeight (weierstrassSpinorPair t a m C z))⁻¹/‖L.basis i‖
    (unitQuaternionFrame (adaptedWeierstrassGeneratorLift ht ha m hC0 i s)).1 =
      (K • fderiv ℝ (F ∘ periodTorusProjection L) z (L.basis i),
       K • fderiv ℝ (F ∘ periodTorusProjection L) z (I*L.basis i)) := by
  exact quaternion_phase_aligns_differential _ _ _
    (harmonic_integer_cap_generator_frame ht ha hc m hC0 hC hX hp hh hg hU hfix hcore i s)
    (generatorHalfPhase_unit _ i) (generatorHalfPhase_square _ i)

theorem generator_spin_normalization_positive {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) {C : ℂ} (hC : C ≠ 0)
    (i : Fin 2) (s : ℝ) :
    0 < (spinorWeight (weierstrassSpinorPair t a m C
      (periodBasisLine (rhombicPeriodPair t ht) i s)))⁻¹/
        ‖(rhombicPeriodPair t ht).basis i‖ := by
  apply div_pos
  · exact inv_pos.mpr (spinorWeight_pos (weierstrassSpinorPair_ne_zero ht ha m hC
      (periodBasisLine_not_mem_lattice _ i s)))
  · exact norm_pos_iff.mpr ((rhombicPeriodPair t ht).basis.ne_zero i)

/-- Every lift of the tangent-adapted frame on the second curve has the
same closure parity as the explicit rotated lift. -/
theorem adapted_second_generator_any_lift_closed_iff
    {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1)
    (m : ℤ) {C : ℂ} (hC : C ≠ 0) {q : unitInterval → UnitQuaternion}
    (hq : Continuous q)
    (hframe : ∀ s, unitQuaternionFrame (q s) =
      unitQuaternionFrame (adaptedWeierstrassGeneratorLift ht ha m hC 1 s)) :
    q 1 = q 0 ↔ Even m := by
  let r : unitInterval → UnitQuaternion := fun s => adaptedWeierstrassGeneratorLift ht ha m hC 1 s
  have hr : Continuous r :=
    (adaptedWeierstrassGeneratorLift_continuous ht ha m hC 1).comp continuous_subtype_val
  have he : unitQuaternionFrame ∘ q = unitQuaternionFrame ∘ r := funext hframe
  rw [quaternion_frame_lifts_closed_iff hq hr he 0 1]
  change adaptedWeierstrassGeneratorLift ht ha m hC 1 1 =
    adaptedWeierstrassGeneratorLift ht ha m hC 1 0 ↔ Even m
  rw [(adaptedWeierstrassGeneratorLift_endpoints ht ha m hC).2]
  by_cases hm : Even m
  · simp only [hm,ite_true,iff_self]
  · simp only [hm,ite_false,unitQuaternionAntipode_ne,iff_self]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_integer_cap_adapted_generator_frame
#print axioms TwoAxisHelicoid.adapted_second_generator_any_lift_closed_iff
