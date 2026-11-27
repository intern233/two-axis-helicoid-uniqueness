import TwoAxisHelicoid.SignCoverConnected
import TwoAxisHelicoid.CompactWeierstrassCover

namespace TwoAxisHelicoid
open Set

/-- The already computed holomorphic-section parity agrees with the
connectedness of the actual compact sign cover. This does not assert
that an arbitrary embedded surface induces an even spin structure. -/
theorem integerSignCover_connected_iff_even_sections {t : ℝ} (ht : 0 < t) (m : ℤ) :
    PathConnectedSpace (LatticeSignCover (rhombicPeriodPair t ht)
      (latticeSpinParity (rhombicPeriodPair t ht) m)) ↔
      Even (Module.finrank ℂ (flatHolomorphicSections t 1 ((-1 : ℂ)^m))) := by
  rw [integerSignCover_pathConnected_iff_odd,integerSpinorSections_even_iff_odd_parameter ht m]

/-- The parity computation transfers to any actual complete cover whose
punctured restriction has been identified with the Weierstrass frame
cover. The complete-cover identification is derived, not assumed. -/
theorem compact_weierstrass_cover_connected_iff_odd
    {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1)
    (m : ℤ) {C : ℂ} (hC : C ≠ 0)
    {E : Type*} [TopologicalSpace E]
    {p : E → PeriodTorus (rhombicPeriodPair t ht)} (hp : IsCoveringMap p)
    (h : QuaternionFramePullback (weierstrassTorusFrame ht ha m hC) ≃ₜ
      {e : E // p e ≠ 0})
    (hh : ∀ q, p (h q).1 = q.1.1.1) : PathConnectedSpace E ↔ Odd m := by
  obtain ⟨H,_,_⟩ := compact_weierstrass_cover_identification ht ha m hC hp h hh
  rw [← integerSignCover_pathConnected_iff_odd (rhombicPeriodPair t ht) m]
  constructor
  · intro hE
    let := hE
    exact H.symm.pathConnectedSpace
  · intro hL
    let := hL
    exact H.pathConnectedSpace

theorem compact_weierstrass_cover_connected_iff_even_sections
    {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1)
    (m : ℤ) {C : ℂ} (hC : C ≠ 0)
    {E : Type*} [TopologicalSpace E]
    {p : E → PeriodTorus (rhombicPeriodPair t ht)} (hp : IsCoveringMap p)
    (h : QuaternionFramePullback (weierstrassTorusFrame ht ha m hC) ≃ₜ
      {e : E // p e ≠ 0})
    (hh : ∀ q, p (h q).1 = q.1.1.1) : PathConnectedSpace E ↔
      Even (Module.finrank ℂ (flatHolomorphicSections t 1 ((-1 : ℂ)^m))) := by
  rw [compact_weierstrass_cover_connected_iff_odd ht ha m hC hp h hh,
    integerSpinorSections_even_iff_odd_parameter ht m]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.integerSignCover_connected_iff_even_sections
#print axioms TwoAxisHelicoid.compact_weierstrass_cover_connected_iff_odd
