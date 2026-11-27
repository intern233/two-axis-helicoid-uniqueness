import TwoAxisHelicoid.ThetaSineFactor
import TwoAxisHelicoid.ThetaQuasiPeriod
import TwoAxisHelicoid.ThetaSymmetry
import TwoAxisHelicoid.RhombicLattice
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaJet

theorem theta_zero_periodic_pi (t : ℝ) :
    Function.Periodic (fun v : ℂ => thetaJet t 0 v = 0) Real.pi := by
  intro v
  apply propext
  dsimp only
  rw [thetaJet_add_pi,neg_eq_zero]

theorem theta_zero_periodic_half {t : ℝ} (ht : 0 < t) :
    Function.Periodic (fun v : ℂ => thetaJet t 0 v = 0) (thetaComplexHalfPeriod t) := by
  intro v
  apply propext
  dsimp only
  rw [thetaJet_zero_quasiperiod ht,mul_eq_zero]
  exact or_iff_right (Complex.exp_ne_zero _)

theorem thetaJet_zero_at_zero (t : ℝ) : thetaJet t 0 0 = 0 := by
  rw [thetaJet_eq_sin_mul_reduced]
  simp

theorem theta_shift_to_strip {t : ℝ} (ht : 0 < t) (v : ℂ) :
    ∃ n : ℤ, |(v-(n:ℂ)*thetaComplexHalfPeriod t).im| ≤ Real.pi*t/4 := by
  let n : ℤ := ⌊2*v.im/(Real.pi*t)+1/2⌋
  refine ⟨n,?_⟩
  have hp : 0 < Real.pi*t := mul_pos Real.pi_pos ht
  have hl := mul_le_mul_of_nonneg_right (Int.floor_le (2*v.im/(Real.pi*t)+1/2)) hp.le
  have hu := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (2*v.im/(Real.pi*t)+1/2)) hp
  rw [add_mul,div_mul_cancel₀ _ hp.ne'] at hl hu
  have hi : (v-(n:ℂ)*thetaComplexHalfPeriod t).im = v.im-(n:ℝ)*(Real.pi*t/2) := by
    simp [thetaComplexHalfPeriod,Complex.mul_im,Complex.mul_re]
  rw [hi,abs_le]
  dsimp [n]
  constructor <;> linarith

theorem thetaJet_zero_iff_period_span {t : ℝ} (ht : 43/50 ≤ t) (v : ℂ) :
    thetaJet t 0 v = 0 ↔ ∃ m n : ℤ, v = (m:ℂ)*Real.pi+(n:ℂ)*thetaComplexHalfPeriod t := by
  have ht0 : 0 < t := by linarith
  constructor
  · intro hv
    obtain ⟨n,hn⟩ := theta_shift_to_strip ht0 v
    have hz := (theta_zero_periodic_half ht0).zsmul n |>.sub_eq v
    simp only [zsmul_eq_mul] at hz
    have hw : thetaJet t 0 (v-(n:ℂ)*thetaComplexHalfPeriod t) = 0 := hz.mpr hv
    obtain ⟨m,hm⟩ := Complex.sin_eq_zero_iff.mp ((thetaJet_zero_iff_sin_on_strip ht hn).mp hw)
    exact ⟨m,n,sub_eq_iff_eq_add.mp hm⟩
  · rintro ⟨m,n,hv⟩
    have h1 := (theta_zero_periodic_half ht0).zsmul n ((m:ℂ)*Real.pi)
    have h2 := (theta_zero_periodic_pi t).zsmul_eq m
    simp only [zsmul_eq_mul] at h1 h2
    rw [hv,h1,h2]
    exact thetaJet_zero_at_zero t

theorem thetaJet_zero_iff_rhombic_lattice {t : ℝ} (ht : 43/50 ≤ t) (z : ℂ) :
    thetaJet t 0 (Real.pi*z/2) = 0 ↔
      z ∈ (rhombicPeriodPair t (by linarith)).lattice := by
  rw [thetaJet_zero_iff_period_span ht,PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m,n,h⟩
    refine ⟨m,n,?_⟩
    change (m:ℂ)*2+(n:ℂ)*(1+I*t) = z
    apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    unfold thetaComplexHalfPeriod at h
    linear_combination -2*h
  · rintro ⟨m,n,h⟩
    refine ⟨m,n,?_⟩
    rw [← h]
    simp only [rhombicPeriodPair,thetaComplexHalfPeriod]
    ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaJet_zero_iff_rhombic_lattice
