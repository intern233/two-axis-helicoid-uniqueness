import TwoAxisHelicoid.PeriodTorusConjugation

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

/-- A genuine nonzero complex scaling of lattices gives a homeomorphism of
their actual quotient tori. -/
noncomputable def periodTorusScalingHomeomorph (L M : PeriodPair) (c : ℂ) (hc : c ≠ 0)
    (hperiod : ∀ z : ℂ, z ∈ L.lattice ↔ c*z ∈ M.lattice) : PeriodTorus L ≃ₜ PeriodTorus M := by
  have hp : ∀ z ω, ω ∈ L.lattice →
      periodTorusProjection M (c*(z+ω)) = periodTorusProjection M (c*z) := by
    intro z ω hω
    rw [mul_add,periodTorusProjection_add_lattice M _ _ ((hperiod ω).mp hω)]
  have hpi : ∀ z ω, ω ∈ M.lattice →
      periodTorusProjection L (c⁻¹*(z+ω)) = periodTorusProjection L (c⁻¹*z) := by
    intro z ω hω
    have hm : c⁻¹*ω ∈ L.lattice := (hperiod _).mpr (by simpa [← mul_assoc,hc] using hω)
    rw [mul_add,periodTorusProjection_add_lattice L _ _ hm]
  refine
    { toFun := periodTorusLift L (fun z => periodTorusProjection M (c*z)) hp
      invFun := periodTorusLift M (fun z => periodTorusProjection L (c⁻¹*z)) hpi
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro q
    obtain ⟨z,rfl⟩ := Quotient.exists_rep q
    change periodTorusProjection L (c⁻¹*(c*z)) = periodTorusProjection L z
    simp [hc]
  · intro q
    obtain ⟨z,rfl⟩ := Quotient.exists_rep q
    change periodTorusProjection M (c*(c⁻¹*z)) = periodTorusProjection M z
    simp [hc]
  · apply continuous_iff_continuousAt.mpr
    intro q
    obtain ⟨z,rfl⟩ := Quotient.exists_rep q
    exact periodTorusLift_continuousAt L _ hp
      ((QuotientAddGroup.continuous_mk.comp (continuous_const.mul continuous_id)).continuousAt)
  · apply continuous_iff_continuousAt.mpr
    intro q
    obtain ⟨z,rfl⟩ := Quotient.exists_rep q
    exact periodTorusLift_continuousAt M _ hpi
      ((QuotientAddGroup.continuous_mk.comp (continuous_const.mul continuous_id)).continuousAt)

@[simp] theorem periodTorusScalingHomeomorph_projection (L M : PeriodPair) (c : ℂ) (hc : c ≠ 0)
    (hperiod : ∀ z : ℂ, z ∈ L.lattice ↔ c*z ∈ M.lattice) (z : ℂ) :
    periodTorusScalingHomeomorph L M c hc hperiod (periodTorusProjection L z) =
      periodTorusProjection M (c*z) := rfl

theorem real_scaling_conjugation_invariant (L M : PeriodPair) {c : ℝ} (hc : c ≠ 0)
    (hperiod : ∀ z : ℂ, z ∈ L.lattice ↔ (c : ℂ)*z ∈ M.lattice)
    (hL : ConjugationInvariantLattice L) : ConjugationInvariantLattice M := by
  intro z hz
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hm : (c : ℂ)⁻¹*z ∈ L.lattice := (hperiod _).mpr (by simpa [← mul_assoc,hcC] using hz)
  have h := (hperiod _).mp (hL _ hm)
  simpa [map_mul,map_inv₀,← mul_assoc,hcC] using h

theorem periodTorusScalingHomeomorph_conjugation (L M : PeriodPair) {c : ℝ} (hc : c ≠ 0)
    (hperiod : ∀ z : ℂ, z ∈ L.lattice ↔ (c : ℂ)*z ∈ M.lattice)
    (hL : ConjugationInvariantLattice L) (hM : ConjugationInvariantLattice M)
    (q : PeriodTorus L) :
    periodTorusScalingHomeomorph L M (c : ℂ) (Complex.ofReal_ne_zero.mpr hc) hperiod
        (periodTorusConjugation L hL q) =
      periodTorusConjugation M hM
        (periodTorusScalingHomeomorph L M (c : ℂ) (Complex.ofReal_ne_zero.mpr hc) hperiod q) := by
  obtain ⟨z,rfl⟩ := Quotient.exists_rep q
  change periodTorusProjection M ((c : ℂ)*conj z) = periodTorusProjection M (conj ((c : ℂ)*z))
  simp

theorem real_scaling_fixed_locus_preconnected (L M : PeriodPair) {c : ℝ} (hc : c ≠ 0)
    (hperiod : ∀ z : ℂ, z ∈ L.lattice ↔ (c : ℂ)*z ∈ M.lattice)
    (hL : ConjugationInvariantLattice L) (hM : ConjugationInvariantLattice M)
    (hconn : IsPreconnected {q : PeriodTorus L | periodTorusConjugation L hL q = q}) :
    IsPreconnected {q : PeriodTorus M | periodTorusConjugation M hM q = q} := by
  let e := periodTorusScalingHomeomorph L M (c : ℂ) (Complex.ofReal_ne_zero.mpr hc) hperiod
  have he : {q : PeriodTorus M | periodTorusConjugation M hM q = q} =
      e '' {q : PeriodTorus L | periodTorusConjugation L hL q = q} := by
    ext q
    constructor
    · intro hq
      obtain ⟨p,rfl⟩ := e.surjective q
      refine ⟨p,?_,rfl⟩
      apply e.injective
      rw [periodTorusScalingHomeomorph_conjugation L M hc hperiod hL hM]
      exact hq
    · rintro ⟨p,hp,rfl⟩
      change periodTorusConjugation M hM
        (periodTorusScalingHomeomorph L M (c : ℂ) (Complex.ofReal_ne_zero.mpr hc) hperiod p) = _
      rw [← periodTorusScalingHomeomorph_conjugation L M hc hperiod hL hM,hp]
  rw [he]
  exact hconn.image e e.continuous.continuousOn

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.real_scaling_fixed_locus_preconnected
