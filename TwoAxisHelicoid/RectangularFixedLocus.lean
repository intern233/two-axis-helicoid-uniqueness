import TwoAxisHelicoid.SlantedLattice
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Connected.TotallyDisconnected

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate
set_option maxHeartbeats 1000000

noncomputable def slantedHeightCos (t : ℝ) (z : ℂ) : ℝ := Real.cos (2*Real.pi*z.im/t)

theorem slantedHeightCos_periodic {t x : ℝ} (ht : 0 < t) (z ω : ℂ)
    (hω : ω ∈ (slantedPeriodPair x t ht).lattice) :
    slantedHeightCos t (z+ω) = slantedHeightCos t z := by
  obtain ⟨_,n,_,hi⟩ := (slanted_mem_lattice_iff ht x ω).mp hω
  unfold slantedHeightCos
  rw [Complex.add_im,hi]
  have he : 2*Real.pi*(z.im+(n : ℝ)*t)/t = 2*Real.pi*z.im/t+(n : ℝ)*(2*Real.pi) := by
    field_simp
  rw [he,Real.cos_add_int_mul_two_pi]

noncomputable def slantedTorusHeightCos {t : ℝ} (ht : 0 < t) (x : ℝ) :
    PeriodTorus (slantedPeriodPair x t ht) → ℝ :=
  periodTorusLift (slantedPeriodPair x t ht) (slantedHeightCos t)
    (slantedHeightCos_periodic ht)

theorem slantedTorusHeightCos_continuous {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Continuous (slantedTorusHeightCos ht x) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨z,rfl⟩ := Quotient.exists_rep q
  exact periodTorusLift_continuousAt _ _ _
    (show ContinuousAt (slantedHeightCos t) z by unfold slantedHeightCos; fun_prop)

theorem slanted_fixed_locus_height_two_values {t x : ℝ} (ht : 0 < t)
    (hL : ConjugationInvariantLattice (slantedPeriodPair x t ht))
    {q : PeriodTorus (slantedPeriodPair x t ht)}
    (hq : periodTorusConjugation (slantedPeriodPair x t ht) hL q = q) :
    slantedTorusHeightCos ht x q = 1 ∨ slantedTorusHeightCos ht x q = -1 := by
  obtain ⟨z,rfl⟩ := Quotient.exists_rep q
  change slantedTorusHeightCos ht x (periodTorusProjection (slantedPeriodPair x t ht) z) = 1 ∨
    slantedTorusHeightCos ht x (periodTorusProjection (slantedPeriodPair x t ht) z) = -1
  have hL := (periodTorusConjugation_fixed_projection_iff _ _ z).mp hq
  obtain ⟨_,n,_,hi⟩ := (slanted_mem_lattice_iff ht x _).mp hL
  simp only [Complex.sub_im,Complex.conj_im,sub_neg_eq_add] at hi
  have he : 2*Real.pi*z.im/t = (n : ℝ)*Real.pi := by
    apply (div_eq_iff ht.ne').mpr
    linear_combination Real.pi*hi
  have ha : |slantedTorusHeightCos ht x (periodTorusProjection (slantedPeriodPair x t ht) z)| = 1 := by
    change |Real.cos (2*Real.pi*z.im/t)| = 1
    rw [he]
    exact Real.abs_cos_int_mul_pi n
  by_cases h : 0 ≤ slantedTorusHeightCos ht x (periodTorusProjection (slantedPeriodPair x t ht) z)
  · exact Or.inl (by simpa only [abs_of_nonneg h] using ha)
  · exact Or.inr (by rw [abs_of_neg (lt_of_not_ge h)] at ha; linarith)

/-- The fixed set of conjugation on a genuine rectangular complex torus is
disconnected. A continuous height character separates its two components. -/
theorem slanted_fixed_locus_not_preconnected_of_vertical_period {t x : ℝ} (ht : 0 < t)
    (hL : ConjugationInvariantLattice (slantedPeriodPair x t ht))
    (hvertical : I*t ∈ (slantedPeriodPair x t ht).lattice) :
    ¬ IsPreconnected {q : PeriodTorus (slantedPeriodPair x t ht) |
      periodTorusConjugation (slantedPeriodPair x t ht) hL q = q} := by
  let L := slantedPeriodPair x t ht
  let S : Set (PeriodTorus L) := {q | periodTorusConjugation L hL q = q}
  let f := slantedTorusHeightCos ht x
  intro hS
  have hpair : ({(1 : ℝ), -1} : Set ℝ).Finite := by simp
  have hfin : (f '' S).Finite := hpair.subset (by
    rintro _ ⟨q,hq,rfl⟩
    rcases slanted_fixed_locus_height_two_values ht hL hq with h | h <;> simp [f,h])
  have hconn : IsPreconnected (f '' S) := hS.image _ (slantedTorusHeightCos_continuous ht x).continuousOn
  have hsub : (f '' S).Subsingleton := (hconn.isDiscrete_iff_subsingleton).mp hfin.isDiscrete
  have hzero : periodTorusProjection L 0 ∈ S := by
    apply (periodTorusConjugation_fixed_projection_iff L _ 0).mpr
    simp
  have hhalf : periodTorusProjection L (I*t/2) ∈ S := by
    apply (periodTorusConjugation_fixed_projection_iff L _ _).mpr
    have he : I*t/2-conj (I*t/2) = I*t := by simp [map_ofNat]; ring
    rw [he]
    exact hvertical
  have hpos : (1 : ℝ) ∈ f '' S := by
    refine ⟨periodTorusProjection L 0,hzero,?_⟩
    change Real.cos (2*Real.pi*(0 : ℂ).im/t) = 1
    simp
  have hneg : (-1 : ℝ) ∈ f '' S := by
    refine ⟨periodTorusProjection L (I*t/2),hhalf,?_⟩
    change Real.cos (2*Real.pi*(I*t/2).im/t) = -1
    have hi : (I*t/2).im = t/2 := by simp [Complex.mul_im]
    rw [hi]
    have he : 2*Real.pi*(t/2)/t = Real.pi := by field_simp
    rw [he,Real.cos_pi]
  have he := hsub hpos hneg
  norm_num at he

theorem rectangular_conjugation_fixed_locus_not_preconnected {t : ℝ} (ht : 0 < t) :
    ¬ IsPreconnected {q : PeriodTorus (rectangularPeriodPair t ht) |
      periodTorusConjugation (rectangularPeriodPair t ht) (rectangular_conjugation_invariant ht) q = q} := by
  apply slanted_fixed_locus_not_preconnected_of_vertical_period ht (rectangular_conjugation_invariant ht)
  simpa [rectangularPeriodPair,slantedPeriodPair] using (rectangularPeriodPair t ht).ω₂_mem_lattice

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.slanted_fixed_locus_not_preconnected_of_vertical_period
#print axioms TwoAxisHelicoid.rectangular_conjugation_fixed_locus_not_preconnected
