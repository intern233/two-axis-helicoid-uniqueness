import TwoAxisHelicoid.ThetaJacobiIdentity
import TwoAxisHelicoid.ThetaZeroSet
import TwoAxisHelicoid.WeierstrassScaling

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaJet

theorem thetaJet_zero_iff_rhombic_lattice_of_pos {t : ℝ} (ht : 0 < t) (z : ℂ) :
    thetaJet t 0 (Real.pi*z/2) = 0 ↔ z ∈ (rhombicPeriodPair t ht).lattice := by
  by_cases hlarge : 43/50 ≤ t
  · exact thetaJet_zero_iff_rhombic_lattice hlarge z
  · have hsmall : t < 43/50 := lt_of_not_ge hlarge
    have hinv : (43/50:ℝ) ≤ 1/t := by
      apply (le_div_iff₀ ht).mpr
      nlinarith
    rw [thetaJet_scaled_zero_iff_reciprocal ht,thetaJet_zero_iff_rhombic_lattice hinv,
      rhombic_reciprocal_mem_iff ht]
    have hi : (I*t:ℂ) ≠ 0 := mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne')
    rw [mul_div_cancel₀ _ hi]

theorem thetaJet_zero_iff_period_span_of_pos {t : ℝ} (ht : 0 < t) (v : ℂ) :
    thetaJet t 0 v = 0 ↔ ∃ m n : ℤ, v = (m:ℂ)*Real.pi+(n:ℂ)*thetaComplexHalfPeriod t := by
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hv : (Real.pi:ℂ)*(2*v/Real.pi)/2 = v := by field_simp
  have hz := thetaJet_zero_iff_rhombic_lattice_of_pos ht (2*v/Real.pi)
  rw [hv] at hz
  rw [hz]
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m,n,he⟩
    refine ⟨m,n,?_⟩
    change (m:ℂ)*2+(n:ℂ)*(1+I*t) = 2*v/Real.pi at he
    calc
      v = (Real.pi:ℂ)*(2*v/Real.pi)/2 := hv.symm
      _ = (Real.pi:ℂ)*((m:ℂ)*2+(n:ℂ)*(1+I*t))/2 := by rw [he]
      _ = _ := by unfold thetaComplexHalfPeriod; ring
  · rintro ⟨m,n,he⟩
    refine ⟨m,n,?_⟩
    change (m:ℂ)*2+(n:ℂ)*(1+I*t) = 2*v/Real.pi
    rw [he]
    unfold thetaComplexHalfPeriod
    field_simp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaJet_zero_iff_rhombic_lattice_of_pos
