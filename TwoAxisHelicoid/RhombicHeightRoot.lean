import TwoAxisHelicoid.RhombicHeightClassification
import TwoAxisHelicoid.VerticalZeroDomain

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology ComplexConjugate
attribute [local irreducible] thetaG verticalA

/-- A real zero of a genuinely normalized meromorphic height coefficient
forces the already constructed vertical root branch and its full allowed
parameter domain. Thus the vertical equation is derived from the data. -/
theorem normalized_height_zero_selects_actual_branch {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) {f g : ℂ → ℂ} {A : ℂ} (hA : A ≠ 0)
    (hf : ∀ z ∉ (rhombicPeriodPair t ht).lattice, DifferentiableAt ℂ f z)
    (hp : ∀ z ω, ω ∈ (rhombicPeriodPair t ht).lattice → f (z+ω)=f z)
    (hg : AnalyticAt ℂ g 0)
    (hloc : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → f z=A/z^2+g z)
    (hconj : ∀ z ∉ (rhombicPeriodPair t ht).lattice, f (conj z)= -conj (f z))
    (hP : (ellipticLinePeriod f (-1) (1+I*t)).re=0) (hzero : f a=0) :
    t < ellipticVerticalUpper ∧ a=verticalA t ∧
      ∃ c : ℝ, c ≠ 0 ∧ ∀ z ∉ (rhombicPeriodPair t ht).lattice,
        f z=I*c*((rhombicPeriodPair t ht).weierstrassP z-
          (rhombicPeriodPair t ht).weierstrassP a) := by
  obtain ⟨c,hc,hform⟩ := rhombic_height_coefficient_classification ht hA hf hp hg hloc hconj hP
  have haL := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2] : a < 2)
  have haz := hform a haL
  rw [hzero] at haz
  have hI : I*(c : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hc)
  have hwp : (rhombicPeriodPair t ht).weierstrassP a=
      ((Real.pi/t-(thetaEtaExpression t).re : ℝ) : ℂ) :=
    sub_eq_zero.mp ((mul_eq_zero.mp haz.symm).resolve_left hI)
  have hη : thetaEtaExpression t=((thetaEtaExpression t).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using thetaEtaExpression_real t
  have hG : thetaG t a=0 := by
    rw [thetaG_eq_weierstrassP_of_pos ht ht a haL,hwp,hη]
    push_cast
    simp only [Complex.ofReal_re]
    ring
  have hbranch := (thetaG_zero_iff_verticalA ht ha).mp hG
  refine ⟨hbranch.1,hbranch.2,c,hc,?_⟩
  intro z hz
  rw [hform z hz,hwp]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.normalized_height_zero_selects_actual_branch
