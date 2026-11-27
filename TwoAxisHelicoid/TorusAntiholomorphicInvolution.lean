import TwoAxisHelicoid.TorusAntiholomorphicLifts

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

theorem torus_antiholomorphic_involution_multiplier (L : PeriodPair)
    {f : PeriodTorus L → PeriodTorus L} (hf : TorusAntiholomorphic L L f)
    (h0 : f 0 = 0) (hinv : Function.Involutive f) :
    ∃ c : ℂ, c*conj c = 1 ∧ (∀ ω ∈ L.lattice, c*conj ω ∈ L.lattice) ∧
      ∀ z, f (periodTorusProjection L z) = periodTorusProjection L (c*conj z) := by
  obtain ⟨c,hcL,hc⟩ := torus_antiholomorphic_fix_zero_antilinear L hf h0
  have hm (z : ℂ) : c*conj (c*conj z)-z ∈ L.lattice := by
    apply (periodTorusProjection_eq_iff L z (c*conj (c*conj z))).mp
    rw [← hc,← hc]
    exact (hinv (periodTorusProjection L z)).symm
  have he := continuous_lattice_valued_constant L
    (show Continuous (fun z : ℂ => c*conj (c*conj z)-z) by fun_prop) hm 1 0
  have hcc : c*conj c = 1 := by simpa [sub_eq_zero] using he
  exact ⟨c,hcc,hcL,hc⟩

theorem antilinear_multiplier_rotation {c : ℂ} (hc : c*conj c = 1) :
    ∃ d : ℂ, d ≠ 0 ∧ d*c = conj d := by
  by_cases hn : c = -1
  · refine ⟨I,Complex.I_ne_zero,?_⟩
    simp [hn]
  · refine ⟨1+conj c,?_,?_⟩
    · intro hz
      have he := congrArg conj hz
      simp only [map_add,map_one,starRingEnd_self_apply,map_zero] at he
      exact hn (by linear_combination he)
    · simp only [map_add,map_one,starRingEnd_self_apply]
      linear_combination hc

theorem antilinear_lattice_rotation_conjugation (L : PeriodPair) {c d : ℂ}
    (hcL : ∀ ω ∈ L.lattice, c*conj ω ∈ L.lattice)
    (hd : d ≠ 0) (hrot : d*c = conj d) :
    ConjugationInvariantLattice (scaledPeriodPair L d hd) := by
  intro z hz
  have hm := (scaledPeriodPair_mem L d hd z).mp hz
  have h := (scaledPeriodPair_mem_iff L d hd (c*conj (d⁻¹*z))).mp (hcL _ hm)
  have he : d*(c*conj (d⁻¹*z)) = conj z := by
    rw [← mul_assoc,hrot,map_mul,map_inv₀]
    simp [hd]
  rwa [he] at h

theorem antilinear_reflection_scaling_commute (L : PeriodPair)
    {f : PeriodTorus L → PeriodTorus L} {c d : ℂ}
    (hc : ∀ z, f (periodTorusProjection L z) = periodTorusProjection L (c*conj z))
    (hd : d ≠ 0) (hrot : d*c = conj d)
    (hM : ConjugationInvariantLattice (scaledPeriodPair L d hd))
    (q : PeriodTorus L) :
    periodTorusScalingHomeomorph L (scaledPeriodPair L d hd) d hd (scaledPeriodPair_mem_iff L d hd)
        (f q) =
      periodTorusConjugation (scaledPeriodPair L d hd) hM
        (periodTorusScalingHomeomorph L (scaledPeriodPair L d hd) d hd
          (scaledPeriodPair_mem_iff L d hd) q) := by
  obtain ⟨z,rfl⟩ := Quotient.exists_rep q
  change periodTorusScalingHomeomorph L (scaledPeriodPair L d hd) d hd (scaledPeriodPair_mem_iff L d hd)
      (f (periodTorusProjection L z)) = _
  rw [hc]
  change periodTorusProjection (scaledPeriodPair L d hd) (d*(c*conj z)) =
    periodTorusProjection (scaledPeriodPair L d hd) (conj (d*z))
  rw [← mul_assoc,hrot,map_mul]

theorem homeomorph_fixed_locus_preconnected {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {f : X → X} {g : Y → Y}
    (he : ∀ x, e (f x) = g (e x)) (hs : IsPreconnected {x | f x = x}) :
    IsPreconnected {y | g y = y} := by
  have hset : {y | g y = y} = e '' {x | f x = x} := by
    ext y
    constructor
    · intro hy
      obtain ⟨x,rfl⟩ := e.surjective y
      refine ⟨x,?_,rfl⟩
      apply e.injective
      rw [he]
      exact hy
    · rintro ⟨x,hx,rfl⟩
      change g (e x) = e x
      rw [← he,hx]
  rw [hset]
  exact hs.image e e.continuous.continuousOn

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.torus_antiholomorphic_involution_multiplier
#print axioms TwoAxisHelicoid.antilinear_lattice_rotation_conjugation
