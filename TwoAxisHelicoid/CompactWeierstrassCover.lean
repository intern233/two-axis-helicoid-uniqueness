import TwoAxisHelicoid.ExtendedCoverDeck

namespace TwoAxisHelicoid
open Set

/-- Any complete torus cover whose punctured restriction is identified
over the base with the actual Weierstrass quaternion-frame pullback is
uniquely isomorphic to the explicit compact sign cover. This proves the
cover-extension step without postulating its uniqueness. Constructing
the ambient induced spin bundle is a separate geometric step. -/
theorem compact_weierstrass_cover_identification
    {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1)
    (m : ℤ) {C : ℂ} (hC : C ≠ 0)
    {E : Type*} [TopologicalSpace E]
    {p : E → PeriodTorus (rhombicPeriodPair t ht)} (hp : IsCoveringMap p)
    (h : QuaternionFramePullback (weierstrassTorusFrame ht ha m hC) ≃ₜ
      {e : E // p e ≠ 0})
    (hh : ∀ q, p (h q).1 = q.1.1.1) :
    ∃! H : LatticeSignCover (rhombicPeriodPair t ht)
      (latticeSpinParity (rhombicPeriodPair t ht) m) ≃ₜ E,
      (∀ q, p (H q) = latticeSignCoverProjection _ _ q) ∧
      ∀ q : PuncturedSignCover (rhombicPeriodPair t ht)
        (latticeSpinParity (rhombicPeriodPair t ht) m),
        H q.1 = (h (weierstrassSpinCoverHomeomorph ht ha m hC q)).1 := by
  let e := (weierstrassSpinCoverHomeomorph ht ha m hC).trans h
  have he (q : PuncturedSignCover (rhombicPeriodPair t ht)
      (latticeSpinParity (rhombicPeriodPair t ht) m)) :
      p (e q).1 = latticeSignCoverProjection _ _ q.1 := by
    change p (h (weierstrassSpinCoverHomeomorph ht ha m hC q)).1 = _
    rw [hh,weierstrassSpinCoverHomeomorph_base]
    rfl
  exact puncturedSignCoverHomeomorph_extends _ _ hp e he

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.compact_weierstrass_cover_identification
