import TwoAxisHelicoid.AssociatedFrameSpin

namespace TwoAxisHelicoid
open Set

theorem puncturedSignCoverDeck_involutive (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    Function.Involutive (puncturedSignCoverDeck L χ) := fun x =>
  Subtype.ext (latticeSignCoverDeck_involutive L χ x.1)

/-- The unit part of the sign multiplier spin bundle is formed using the
diagonal sign relation on the two-sheet cover times the unit circle. -/
abbrev PuncturedMultiplierSpinBundle (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :=
  AssociatedFrameSpin (puncturedSignCoverDeck L χ) (puncturedSignCoverDeck_involutive L χ)

noncomputable def weierstrassFrameSpinHomeomorph
    {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1)
    (m : ℤ) {C : ℂ} (hC : C ≠ 0) :
    PuncturedMultiplierSpinBundle (rhombicPeriodPair t ht)
      (latticeSpinParity (rhombicPeriodPair t ht) m) ≃ₜ
      QuaternionFramePullback (rotatedFrameFamily (weierstrassTorusFrame ht ha m hC)) :=
  associatedFrameSpinHomeomorph _ (weierstrassTorusFrame_continuous ht ha m hC) _
    (puncturedSignCoverDeck_involutive _ _) (weierstrassSpinCoverHomeomorph ht ha m hC)
    (signCoverQuaternionHomeomorph_deck _ _ _ (weierstrassUnitLift_equivariant ht ha m hC)
      (weierstrassUnitLift_continuous ht ha m hC))

theorem weierstrassFrameSpinHomeomorph_over_frames
    {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1)
    (m : ℤ) {C : ℂ} (hC : C ≠ 0)
    (x : PuncturedSignCover (rhombicPeriodPair t ht)
      (latticeSpinParity (rhombicPeriodPair t ht) m)) (u : Circle) :
    (weierstrassFrameSpinHomeomorph ht ha m hC (Quotient.mk _ (x,u))).1.1 =
      (puncturedSignCoverProjection _ _ x,u^2) := by
  exact Prod.ext (weierstrassSpinCoverHomeomorph_base ht ha m hC x) rfl

theorem weierstrassFrameSpinHomeomorph_equivariant
    {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1)
    (m : ℤ) {C : ℂ} (hC : C ≠ 0)
    (v : Circle) (x : PuncturedMultiplierSpinBundle (rhombicPeriodPair t ht)
      (latticeSpinParity (rhombicPeriodPair t ht) m)) :
    (weierstrassFrameSpinHomeomorph ht ha m hC
      (associatedSpinPhase _ (puncturedSignCoverDeck_involutive _ _) v x)).1.2 =
      spinCircleAction v (weierstrassFrameSpinHomeomorph ht ha m hC x).1.2 :=
  associatedFrameSpinHomeomorph_phase _ (weierstrassTorusFrame_continuous ht ha m hC) _
    (puncturedSignCoverDeck_involutive _ _) (weierstrassSpinCoverHomeomorph ht ha m hC)
    (signCoverQuaternionHomeomorph_deck _ _ _ (weierstrassUnitLift_equivariant ht ha m hC)
      (weierstrassUnitLift_continuous ht ha m hC)) v x

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.weierstrassFrameSpinHomeomorph
#print axioms TwoAxisHelicoid.weierstrassFrameSpinHomeomorph_equivariant
