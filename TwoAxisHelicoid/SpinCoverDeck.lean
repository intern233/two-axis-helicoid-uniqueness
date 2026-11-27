import TwoAxisHelicoid.QuaternionSpinPullback

namespace TwoAxisHelicoid
open Set Topology

noncomputable def puncturedSignCoverDeck (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    PuncturedSignCover L χ ≃ₜ PuncturedSignCover L χ :=
  (latticeSignCoverDeck L χ).subtype (fun q => by
    rw [latticeSignCoverProjection_deck])

theorem puncturedSignCoverDeck_mk (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (v : PuncturedLatticePlane L × ZMod 2) :
    puncturedSignCoverDeck L χ (puncturedSignCoverMk L χ v) =
      puncturedSignCoverMk L χ (v.1,v.2+1) := by
  apply Subtype.ext
  exact latticeSignCoverDeck_mk L χ (v.1.1,v.2)

noncomputable def unitQuaternionAntipode : UnitQuaternion ≃ₜ UnitQuaternion :=
  (unitSpinorQuaternionHomeomorph.symm.trans unitSpinorAntipode).trans unitSpinorQuaternionHomeomorph

theorem unitQuaternionAntipode_spinor (s : UnitSpinor) :
    unitQuaternionAntipode (unitSpinorQuaternionHomeomorph s) =
      unitSpinorQuaternionHomeomorph (unitSpinorAntipode s) := by
  change unitSpinorQuaternionHomeomorph
    (unitSpinorAntipode (unitSpinorQuaternionHomeomorph.symm (unitSpinorQuaternionHomeomorph s))) = _
  rw [unitSpinorQuaternionHomeomorph.symm_apply_apply]

theorem unitQuaternionAntipode_val (q : UnitQuaternion) :
    (unitQuaternionAntipode q).1 = -q.1 := by
  obtain ⟨s,rfl⟩ := unitSpinorQuaternionHomeomorph.surjective q
  rw [unitQuaternionAntipode_spinor]
  change spinorQuaternionLinearEquiv (-s.1) = -spinorQuaternionLinearEquiv s.1
  exact map_neg _ _

theorem unitQuaternionFrame_antipode (q : UnitQuaternion) :
    unitQuaternionFrame (unitQuaternionAntipode q) = unitQuaternionFrame q := by
  obtain ⟨s,rfl⟩ := unitSpinorQuaternionHomeomorph.surjective q
  rw [unitQuaternionAntipode_spinor,unitQuaternionFrame_spinor,unitQuaternionFrame_spinor]
  exact unitSpinorTangentFrame_fibers.mpr (Or.inr rfl)

noncomputable def quaternionFramePullbackDeck {B : Type*} [TopologicalSpace B]
    (f : B → OrthonormalTangentPair) :
    QuaternionFramePullback f ≃ₜ QuaternionFramePullback f :=
  ((Homeomorph.refl B).prodCongr unitQuaternionAntipode).subtype (fun v => by
    change f v.1 = unitQuaternionFrame v.2 ↔
      f v.1 = unitQuaternionFrame (unitQuaternionAntipode v.2)
    rw [unitQuaternionFrame_antipode])

theorem signCoverQuaternionHomeomorph_mk (L : PeriodPair)
    (χ : L.lattice →+ ZMod 2) (s : PuncturedLatticePlane L → UnitSpinor)
    (hs : UnitSpinorEquivariant L χ s) (hc : Continuous s)
    (v : PuncturedLatticePlane L × ZMod 2) :
    (signCoverQuaternionHomeomorph L χ s hs hc (puncturedSignCoverMk L χ v)).1 =
      (puncturedPlaneProjection L v.1,unitSpinorQuaternionHomeomorph (v.2 +ᵥ s v.1)) := by
  change (spinorQuaternionPullbackHomeomorph (equivariantTorusFrame L s)
    (signCoverToFramePullback L χ s hs (puncturedSignCoverMk L χ v))).1 = _
  rw [signCoverToFramePullback_mk]
  rfl

/-- The identification respects the nontrivial deck transformation, so
it is an isomorphism of the two principal sign covers over the torus. -/
theorem signCoverQuaternionHomeomorph_deck (L : PeriodPair)
    (χ : L.lattice →+ ZMod 2) (s : PuncturedLatticePlane L → UnitSpinor)
    (hs : UnitSpinorEquivariant L χ s) (hc : Continuous s) (q : PuncturedSignCover L χ) :
    signCoverQuaternionHomeomorph L χ s hs hc (puncturedSignCoverDeck L χ q) =
      quaternionFramePullbackDeck (equivariantTorusFrame L s)
        (signCoverQuaternionHomeomorph L χ s hs hc q) := by
  obtain ⟨v,rfl⟩ := puncturedSignCoverMk_surjective L χ q
  apply Subtype.ext
  rw [puncturedSignCoverDeck_mk,signCoverQuaternionHomeomorph_mk]
  change (puncturedPlaneProjection L v.1,unitSpinorQuaternionHomeomorph ((v.2+1) +ᵥ s v.1)) =
    (id _,unitQuaternionAntipode
      (signCoverQuaternionHomeomorph L χ s hs hc (puncturedSignCoverMk L χ v)).1.2)
  rw [signCoverQuaternionHomeomorph_mk,unitQuaternionAntipode_spinor]
  apply Prod.ext
  · change puncturedPlaneProjection L v.1 =
      (signCoverQuaternionHomeomorph L χ s hs hc (puncturedSignCoverMk L χ v)).1.1
    rw [signCoverQuaternionHomeomorph_base]
    rfl
  · apply congrArg unitSpinorQuaternionHomeomorph
    rw [add_comm v.2 1,add_vadd,unitSpinor_vadd_one]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.signCoverQuaternionHomeomorph_deck

