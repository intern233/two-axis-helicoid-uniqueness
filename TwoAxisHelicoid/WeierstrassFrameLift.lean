import TwoAxisHelicoid.SpinorLatticeCharacter
import TwoAxisHelicoid.SpinorRegularity
import TwoAxisHelicoid.NormalizedSpinorFrame
import TwoAxisHelicoid.PuncturedLatticePlane

namespace TwoAxisHelicoid
open Complex Set
set_option maxHeartbeats 1000000

noncomputable def weierstrassSpinorPair (t a : ℝ) (m : ℤ) (C z : ℂ) : ℂ × ℂ :=
  (weierstrassSpinorOne t a m C z,weierstrassSpinorTwo t a m C z)

theorem weierstrassSpinorPair_quadratic (t a : ℝ) (m : ℤ) (C z : ℂ) :
    spinorQuadratic (weierstrassSpinorPair t a m C z) = spinorCoordinateData t a m C z := rfl

theorem weierstrassSpinorPair_ne_zero {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1)
    (m : ℤ) {C z : ℂ} (hC : C ≠ 0) (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    weierstrassSpinorPair t a m C z ≠ 0 := by
  intro he
  rcases weierstrassSpinor_pair_not_both_zero ht ha m hC hz with h | h
  · exact h (congrArg Prod.fst he)
  · exact h (congrArg Prod.snd he)

theorem latticeSpinParity_sign_neg (L : PeriodPair) (m : ℤ) (ω : L.lattice) :
    paritySign (latticeSpinParity L (-m) ω) = paritySign (latticeSpinParity L m ω) := by
  rw [latticeSpinParity_sign,latticeSpinParity_sign]
  simp [integerSpinCharacter,neg_one_zpow_eq_ite]
  split_ifs <;> norm_num

theorem weierstrassSpinorPair_multiplier {t a : ℝ} (ht : 0 < t) (m : ℤ)
    (C z : ℂ) (ω : (rhombicPeriodPair t ht).lattice) :
    weierstrassSpinorPair t a m C (z+ω.1) =
      paritySign (latticeSpinParity (rhombicPeriodPair t ht) m ω) •
        weierstrassSpinorPair t a m C z := by
  apply Prod.ext
  · change C*thetaSpinor t a m (z+ω.1) =
      paritySign (latticeSpinParity (rhombicPeriodPair t ht) m ω)*(C*thetaSpinor t a m z)
    rw [thetaSpinor_multiplier_lattice ht m]
    ring
  · change -I*C*thetaSpinor t (-a) (-m) (z+ω.1) =
      paritySign (latticeSpinParity (rhombicPeriodPair t ht) m ω)*(-I*C*thetaSpinor t (-a) (-m) z)
    rw [thetaSpinor_multiplier_lattice ht (-m),latticeSpinParity_sign_neg]
    ring

theorem normalizeSpinor_parity {s t : NonzeroSpinor} (g : ZMod 2)
    (ht : t.1 = paritySign g • s.1) :
    normalizeSpinor t = g +ᵥ normalizeSpinor s := by
  rcases zmod_two_cases g with rfl | rfl
  · rw [paritySign_zero,one_smul] at ht
    rw [zero_vadd]
    exact congrArg normalizeSpinor (Subtype.ext ht)
  · rw [paritySign_one,neg_one_smul] at ht
    rw [unitSpinor_vadd_one]
    have he : t = ⟨-s.1,neg_ne_zero.mpr s.2⟩ := Subtype.ext ht
    rw [he]
    exact normalizeSpinor_neg s

noncomputable def weierstrassNonzeroSpinors {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1)
    (m : ℤ) {C : ℂ} (hC : C ≠ 0) :
    PuncturedLatticePlane (rhombicPeriodPair t ht) → NonzeroSpinor :=
  fun z => ⟨weierstrassSpinorPair t a m C z.1,weierstrassSpinorPair_ne_zero ht ha m hC z.2⟩

theorem weierstrassNonzeroSpinors_continuous {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) {C : ℂ} (hC : C ≠ 0) :
    Continuous (weierstrassNonzeroSpinors ht ha m hC) := by
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro z
  obtain ⟨h1,h2⟩ := weierstrassSpinors_analyticAt ht m C z.2
  exact (h1.continuousAt.prodMk h2.continuousAt).comp continuous_subtype_val.continuousAt

noncomputable def weierstrassUnitLift {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1)
    (m : ℤ) {C : ℂ} (hC : C ≠ 0) :
    PuncturedLatticePlane (rhombicPeriodPair t ht) → UnitSpinor :=
  normalizeSpinor ∘ weierstrassNonzeroSpinors ht ha m hC

theorem weierstrassUnitLift_continuous {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) {C : ℂ} (hC : C ≠ 0) :
    Continuous (weierstrassUnitLift ht ha m hC) :=
  normalizeSpinor_continuous.comp (weierstrassNonzeroSpinors_continuous ht ha m hC)

theorem weierstrassUnitLift_equivariant {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) {C : ℂ} (hC : C ≠ 0)
    (ω : (rhombicPeriodPair t ht).lattice)
    (z w : PuncturedLatticePlane (rhombicPeriodPair t ht)) (hw : w.1 = z.1+ω.1) :
    weierstrassUnitLift ht ha m hC w =
      latticeSpinParity (rhombicPeriodPair t ht) m ω +ᵥ weierstrassUnitLift ht ha m hC z := by
  apply normalizeSpinor_parity
  change weierstrassSpinorPair t a m C w.1 = _
  rw [hw]
  exact weierstrassSpinorPair_multiplier ht m C z.1 ω

theorem weierstrassUnitLift_vectors {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) {C : ℂ} (hC : C ≠ 0)
    (z : PuncturedLatticePlane (rhombicPeriodPair t ht)) :
    (unitSpinorTangentFrame (weierstrassUnitLift ht ha m hC z)).1 =
      ((spinorWeight (weierstrassSpinorPair t a m C z.1))⁻¹ •
          nullRealDerivative (spinorCoordinateData t a m C z.1) 1,
       (spinorWeight (weierstrassSpinorPair t a m C z.1))⁻¹ •
          nullRealDerivative (spinorCoordinateData t a m C z.1) I) :=
  normalizedSpinorFrame_vectors (weierstrassNonzeroSpinors ht ha m hC z)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.weierstrassUnitLift_equivariant
#print axioms TwoAxisHelicoid.weierstrassUnitLift_vectors

