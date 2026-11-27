import TwoAxisHelicoid.PeriodTorusConjugation
import TwoAxisHelicoid.RhombicRegularPaths

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

theorem rhombicConjugationInvariant {t : ℝ} (ht : 0 < t) :
    ConjugationInvariantLattice (rhombicPeriodPair t ht) := fun _ hz => rhombic_conj_mem ht hz

noncomputable def rhombicHorizontalReflection {t : ℝ} (ht : 0 < t) :
    PeriodTorus (rhombicPeriodPair t ht) → PeriodTorus (rhombicPeriodPair t ht) :=
  periodTorusConjugation _ (rhombicConjugationInvariant ht)

noncomputable def rhombicVerticalReflection {t : ℝ} (ht : 0 < t) :
    PeriodTorus (rhombicPeriodPair t ht) → PeriodTorus (rhombicPeriodPair t ht) :=
  fun q => -rhombicHorizontalReflection ht q

@[simp] theorem rhombicHorizontalReflection_projection {t : ℝ} (ht : 0 < t) (z : ℂ) :
    rhombicHorizontalReflection ht (periodTorusProjection (rhombicPeriodPair t ht) z) =
      periodTorusProjection (rhombicPeriodPair t ht) (conj z) := rfl

@[simp] theorem rhombicVerticalReflection_projection {t : ℝ} (ht : 0 < t) (z : ℂ) :
    rhombicVerticalReflection ht (periodTorusProjection (rhombicPeriodPair t ht) z) =
      periodTorusProjection (rhombicPeriodPair t ht) (-conj z) := rfl

theorem rhombic_horizontal_fixed_iff_real {t : ℝ} (ht : 0 < t)
    (q : PeriodTorus (rhombicPeriodPair t ht)) :
    rhombicHorizontalReflection ht q = q ↔
      ∃ x : ℝ, periodTorusProjection (rhombicPeriodPair t ht) (x : ℂ) = q := by
  obtain ⟨z,rfl⟩ := Quotient.exists_rep q
  change rhombicHorizontalReflection ht (periodTorusProjection _ z) = periodTorusProjection _ z ↔ _
  rw [rhombicHorizontalReflection_projection,periodTorusProjection_eq_iff,
    rhombic_mem_lattice_iff ht]
  constructor
  · rintro ⟨m,n,hr,hi⟩
    simp only [Complex.sub_re,Complex.conj_re,sub_self,Complex.sub_im,
      Complex.conj_im,sub_neg_eq_add] at hr hi
    have hn : (n : ℝ) = -2*(m : ℝ) := by linarith
    have hz : z.im = -(m : ℝ)*t := by rw [hn] at hi; linarith
    refine ⟨z.re+(m : ℝ),?_⟩
    apply (periodTorusProjection_eq_iff _ _ _).mpr
    apply (rhombic_mem_lattice_iff ht _).mpr
    refine ⟨0,-m,?_,?_⟩
    · simp [Complex.sub_re]
    · simp [Complex.sub_im,hz]
  · rintro ⟨x,hx⟩
    have hfix : rhombicHorizontalReflection ht (periodTorusProjection _ (x : ℂ)) =
        periodTorusProjection (rhombicPeriodPair t ht) (x : ℂ) := by
      rw [rhombicHorizontalReflection_projection,Complex.conj_ofReal]
    rw [hx] at hfix
    exact (rhombic_mem_lattice_iff ht _).mp
      ((periodTorusConjugation_fixed_projection_iff _ _ z).mp hfix)

theorem rhombic_vertical_fixed_projection_iff {t : ℝ} (ht : 0 < t) (z : ℂ) :
    rhombicVerticalReflection ht (periodTorusProjection (rhombicPeriodPair t ht) z) =
      periodTorusProjection (rhombicPeriodPair t ht) z ↔
      ∃ n : ℤ, z.re = (n : ℝ) := by
  rw [rhombicVerticalReflection_projection,periodTorusProjection_eq_iff,
    rhombic_mem_lattice_iff ht]
  simp only [sub_neg_eq_add,Complex.add_re,Complex.conj_re,Complex.add_im,
    Complex.conj_im,add_neg_cancel]
  constructor
  · rintro ⟨m,n,hr,hi⟩
    have hn : (n : ℝ) = 0 := (mul_eq_zero.mp hi.symm).resolve_right ht.ne'
    refine ⟨m,?_⟩
    rw [hn] at hr
    linarith
  · rintro ⟨m,hm⟩
    refine ⟨m,0,?_,by simp⟩
    simp [hm,two_mul]

theorem rhombic_vertical_fixed_iff_imaginary {t : ℝ} (ht : 0 < t)
    (q : PeriodTorus (rhombicPeriodPair t ht)) :
    rhombicVerticalReflection ht q = q ↔
      ∃ y : ℝ, periodTorusProjection (rhombicPeriodPair t ht) (I*y) = q := by
  obtain ⟨z,rfl⟩ := Quotient.exists_rep q
  change rhombicVerticalReflection ht (periodTorusProjection _ z) = periodTorusProjection _ z ↔ _
  rw [rhombic_vertical_fixed_projection_iff ht]
  constructor
  · rintro ⟨m,hm⟩
    refine ⟨z.im-(m : ℝ)*t,?_⟩
    apply (periodTorusProjection_eq_iff _ _ _).mpr
    apply (rhombic_mem_lattice_iff ht _).mpr
    refine ⟨0,m,?_,?_⟩
    · simp [Complex.sub_re,Complex.mul_re,hm]
    · simp [Complex.sub_im,Complex.mul_im]
  · rintro ⟨y,hy⟩
    have hfix := (rhombic_vertical_fixed_projection_iff ht (I*y)).mpr
      ⟨0,by simp [Complex.mul_re]⟩
    rw [hy] at hfix
    exact (rhombic_vertical_fixed_projection_iff ht z).mp hfix

theorem rhombic_horizontal_fixed_locus_connected {t : ℝ} (ht : 0 < t) :
    IsConnected {q : PeriodTorus (rhombicPeriodPair t ht) | rhombicHorizontalReflection ht q = q} := by
  have he : {q : PeriodTorus (rhombicPeriodPair t ht) | rhombicHorizontalReflection ht q = q} =
      Set.range (fun x : ℝ => periodTorusProjection (rhombicPeriodPair t ht) (x : ℂ)) := by
    ext q
    exact rhombic_horizontal_fixed_iff_real ht q
  rw [he]
  exact isConnected_range ((QuotientAddGroup.continuous_mk).comp Complex.continuous_ofReal)

theorem rhombic_vertical_fixed_locus_connected {t : ℝ} (ht : 0 < t) :
    IsConnected {q : PeriodTorus (rhombicPeriodPair t ht) | rhombicVerticalReflection ht q = q} := by
  have he : {q : PeriodTorus (rhombicPeriodPair t ht) | rhombicVerticalReflection ht q = q} =
      Set.range (fun y : ℝ => periodTorusProjection (rhombicPeriodPair t ht) (I*y)) := by
    ext q
    exact rhombic_vertical_fixed_iff_imaginary ht q
  rw [he]
  apply isConnected_range
  exact (QuotientAddGroup.continuous_mk).comp (by fun_prop)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rhombic_horizontal_fixed_locus_connected
#print axioms TwoAxisHelicoid.rhombic_vertical_fixed_locus_connected
