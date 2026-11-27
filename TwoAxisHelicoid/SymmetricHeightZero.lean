import TwoAxisHelicoid.SymmetricNullDifferential
import TwoAxisHelicoid.WeierstrassSurjectivity
import TwoAxisHelicoid.WeierstrassFibers
import TwoAxisHelicoid.RhombicFixedLoci

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

theorem symmetric_height_zero_is_horizontal_fixed {t : ℝ} (ht : 0 < t)
    {p : ℂ → Fin 3 → ℂ} (hp : TwoAxisNullDifferential (rhombicPeriodPair t ht) p)
    {K u : ℂ} (hK : K ≠ 0)
    (hheight : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      p z 2 = K*((rhombicPeriodPair t ht).weierstrassP z-u))
    {z : ℂ} (hz : z ∉ (rhombicPeriodPair t ht).lattice) (hzero : p z 2 = 0) :
    rhombicHorizontalReflection ht (periodTorusProjection (rhombicPeriodPair t ht) z) =
      periodTorusProjection (rhombicPeriodPair t ht) z := by
  have hcz : conj z ∉ (rhombicPeriodPair t ht).lattice := by
    intro h
    have hh := rhombic_conj_mem ht h
    exact hz (by simpa using hh)
  have hczero : p (conj z) 2 = 0 := by
    have h := congrFun (hp.conjugation z hz) 2
    change p (conj z) 2 = -conj (p z 2) at h
    simpa [hzero] using h
  have hzval : (rhombicPeriodPair t ht).weierstrassP z = u := by
    rw [hheight z hz] at hzero
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hK)
  have hczval : (rhombicPeriodPair t ht).weierstrassP (conj z) = u := by
    rw [hheight _ hcz] at hczero
    exact sub_eq_zero.mp ((mul_eq_zero.mp hczero).resolve_left hK)
  have hfiber := (rhombic_weierstrassP_eq_iff ht hz hcz).mp (hczval.trans hzval.symm)
  have hm : conj z-z ∈ (rhombicPeriodPair t ht).lattice :=
    hfiber.resolve_right (hp.height_zero_not_vertical_fixed hz hzero)
  apply (periodTorusConjugation_fixed_projection_iff _ _ z).mpr
  simpa only [neg_sub] using (rhombicPeriodPair t ht).lattice.neg_mem hm

theorem symmetric_height_has_real_zero {t : ℝ} (ht : 0 < t)
    {p : ℂ → Fin 3 → ℂ} (hp : TwoAxisNullDifferential (rhombicPeriodPair t ht) p)
    {K u : ℂ} (hK : K ≠ 0)
    (hheight : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      p z 2 = K*((rhombicPeriodPair t ht).weierstrassP z-u)) :
    ∃ x : ℝ, (x : ℂ) ∉ (rhombicPeriodPair t ht).lattice ∧
      p x 2 = 0 ∧ 2*(x : ℂ) ∉ (rhombicPeriodPair t ht).lattice := by
  let L := rhombicPeriodPair t ht
  obtain ⟨z,hz,hzu⟩ := weierstrassP_attains_every_finite_value L u
  have hzero : p z 2 = 0 := by rw [hheight z hz,hzu]; ring
  have hfix := symmetric_height_zero_is_horizontal_fixed ht hp hK hheight hz hzero
  obtain ⟨x,hx⟩ := (rhombic_horizontal_fixed_iff_real ht (periodTorusProjection L z)).mp hfix
  have hdiff := (periodTorusProjection_eq_iff L (x : ℂ) z).mp hx
  have hxn : (x : ℂ) ∉ L.lattice := by
    intro h
    apply hz
    simpa only [add_sub_cancel] using L.lattice.add_mem h hdiff
  have he : p z = p x := by
    simpa only [add_sub_cancel] using hp.periodic (x : ℂ) (z-x) hdiff
  have hxzero : p x 2 = 0 := by rw [← he]; exact hzero
  exact ⟨x,hxn,hxzero,hp.height_zero_not_two_torsion hxn hxzero⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.symmetric_height_has_real_zero
