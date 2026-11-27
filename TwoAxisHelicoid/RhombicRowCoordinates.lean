import TwoAxisHelicoid.RhombicRegularPaths
import Mathlib.Algebra.Order.Floor.Ring

namespace TwoAxisHelicoid
open Complex Set
set_option maxHeartbeats 1000000

noncomputable def rhombicRowIndex (t : ℝ) (z : ℂ) : ℤ := ⌊z.im/t⌋
noncomputable def rhombicRowPoint (t : ℝ) (z : ℂ) : ℂ :=
  z-(rhombicRowIndex t z : ℂ)*(1+I*t)
noncomputable def rhombicGapIndex (t : ℝ) (z : ℂ) : ℤ :=
  ⌊(rhombicRowPoint t z).re/2⌋+1
noncomputable def rhombicGapPoint (t : ℝ) (z : ℂ) : ℂ :=
  rhombicRowPoint t z-(rhombicGapIndex t z : ℂ)*2

theorem rhombicRowPoint_im (t : ℝ) (z : ℂ) :
    (rhombicRowPoint t z).im = z.im-(rhombicRowIndex t z : ℝ)*t := by
  simp [rhombicRowPoint,Complex.mul_im]

theorem rhombicRowPoint_re (t : ℝ) (z : ℂ) :
    (rhombicRowPoint t z).re = z.re-(rhombicRowIndex t z : ℝ) := by
  simp [rhombicRowPoint,Complex.mul_re,Complex.mul_im]

theorem rhombicRowIndex_eq_iff {t : ℝ} (ht : 0 < t) (z : ℂ) (n : ℤ) :
    rhombicRowIndex t z = n ↔ (n : ℝ)*t ≤ z.im ∧ z.im < ((n : ℝ)+1)*t := by
  unfold rhombicRowIndex
  rw [Int.floor_eq_iff,le_div_iff₀ ht,div_lt_iff₀ ht]

theorem rhombicRowPoint_im_bounds {t : ℝ} (ht : 0 < t) (z : ℂ) :
    0 ≤ (rhombicRowPoint t z).im ∧ (rhombicRowPoint t z).im < t := by
  have h := (rhombicRowIndex_eq_iff ht z (rhombicRowIndex t z)).mp rfl
  rw [rhombicRowPoint_im]
  constructor <;> nlinarith [h.1,h.2]

theorem rhombicRowIndex_add_half {t : ℝ} (ht : 0 < t) (z : ℂ) :
    rhombicRowIndex t (z+(1+I*t)) = rhombicRowIndex t z+1 := by
  unfold rhombicRowIndex
  have he : (z+(1+I*t)).im/t = z.im/t+1 := by
    simp only [Complex.add_im,Complex.one_im,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add]
    field_simp
  rw [he,Int.floor_add_one]

theorem rhombicRowPoint_add_half {t : ℝ} (ht : 0 < t) (z : ℂ) :
    rhombicRowPoint t (z+(1+I*t)) = rhombicRowPoint t z := by
  unfold rhombicRowPoint
  rw [rhombicRowIndex_add_half ht z]
  push_cast
  ring

theorem rhombicRowIndex_add_two (t : ℝ) (z : ℂ) :
    rhombicRowIndex t (z+2) = rhombicRowIndex t z := by
  simp [rhombicRowIndex]

theorem rhombicRowPoint_add_two (t : ℝ) (z : ℂ) :
    rhombicRowPoint t (z+2) = rhombicRowPoint t z+2 := by
  unfold rhombicRowPoint
  rw [rhombicRowIndex_add_two]
  ring

theorem rhombicGapIndex_add_half {t : ℝ} (ht : 0 < t) (z : ℂ) :
    rhombicGapIndex t (z+(1+I*t)) = rhombicGapIndex t z := by
  unfold rhombicGapIndex
  rw [rhombicRowPoint_add_half ht z]

theorem rhombicGapPoint_add_half {t : ℝ} (ht : 0 < t) (z : ℂ) :
    rhombicGapPoint t (z+(1+I*t)) = rhombicGapPoint t z := by
  unfold rhombicGapPoint
  rw [rhombicRowPoint_add_half ht z,rhombicGapIndex_add_half ht z]

theorem rhombicGapIndex_add_two (t : ℝ) (z : ℂ) :
    rhombicGapIndex t (z+2) = rhombicGapIndex t z+1 := by
  unfold rhombicGapIndex
  rw [rhombicRowPoint_add_two]
  have he : (rhombicRowPoint t z+2).re/2 = (rhombicRowPoint t z).re/2+1 := by simp; ring
  rw [he,Int.floor_add_one]

theorem rhombicGapPoint_add_two (t : ℝ) (z : ℂ) :
    rhombicGapPoint t (z+2) = rhombicGapPoint t z := by
  unfold rhombicGapPoint
  rw [rhombicRowPoint_add_two,rhombicGapIndex_add_two]
  push_cast
  ring

theorem rhombicGapPoint_re_bounds (t : ℝ) (z : ℂ) :
    -2 ≤ (rhombicGapPoint t z).re ∧ (rhombicGapPoint t z).re < 0 := by
  have h₁ := Int.floor_le ((rhombicRowPoint t z).re/2)
  have h₂ := Int.lt_floor_add_one ((rhombicRowPoint t z).re/2)
  simp only [rhombicGapPoint,Complex.sub_re,Complex.mul_re,Complex.intCast_re,
    Complex.intCast_im,zero_mul,sub_zero]
  unfold rhombicGapIndex
  push_cast
  norm_num
  constructor <;> linarith

theorem rhombicGapPoint_im (t : ℝ) (z : ℂ) :
    (rhombicGapPoint t z).im = (rhombicRowPoint t z).im := by
  simp [rhombicGapPoint]

theorem rhombicRowPoint_lattice_iff {t : ℝ} (ht : 0 < t) (z : ℂ) :
    rhombicRowPoint t z ∈ (rhombicPeriodPair t ht).lattice ↔ z ∈ (rhombicPeriodPair t ht).lattice := by
  have hn : (rhombicRowIndex t z : ℂ)*(1+I*t) ∈ (rhombicPeriodPair t ht).lattice := by
    simpa only [zsmul_eq_mul,rhombicPeriodPair] using
      (rhombicPeriodPair t ht).lattice.smul_mem (rhombicRowIndex t z) (rhombicPeriodPair t ht).ω₂_mem_lattice
  constructor
  · intro h
    have he : rhombicRowPoint t z+(rhombicRowIndex t z : ℂ)*(1+I*t) = z := by
      simp only [rhombicRowPoint,sub_add_cancel]
    exact he ▸ (rhombicPeriodPair t ht).lattice.add_mem h hn
  · intro h
    exact (rhombicPeriodPair t ht).lattice.sub_mem h hn

theorem rhombicGapPoint_lattice_iff {t : ℝ} (ht : 0 < t) (z : ℂ) :
    rhombicGapPoint t z ∈ (rhombicPeriodPair t ht).lattice ↔ z ∈ (rhombicPeriodPair t ht).lattice := by
  have hm : (rhombicGapIndex t z : ℂ)*2 ∈ (rhombicPeriodPair t ht).lattice := by
    simpa only [zsmul_eq_mul,rhombicPeriodPair] using
      (rhombicPeriodPair t ht).lattice.smul_mem (rhombicGapIndex t z) (rhombicPeriodPair t ht).ω₁_mem_lattice
  rw [← rhombicRowPoint_lattice_iff ht z]
  constructor
  · intro h
    have he : rhombicGapPoint t z+(rhombicGapIndex t z : ℂ)*2 = rhombicRowPoint t z := by
      simp only [rhombicGapPoint,sub_add_cancel]
    exact he ▸ (rhombicPeriodPair t ht).lattice.add_mem h hm
  · intro h
    exact (rhombicPeriodPair t ht).lattice.sub_mem h hm

theorem rhombicGapPoint_re_strict_of_row {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) (hrow : (rhombicRowPoint t z).im = 0) :
    -2 < (rhombicGapPoint t z).re ∧ (rhombicGapPoint t z).re < 0 := by
  have hb := rhombicGapPoint_re_bounds t z
  refine ⟨lt_of_le_of_ne hb.1 ?_,hb.2⟩
  intro he
  have hpoint : rhombicGapPoint t z = -2 := by
    apply Complex.ext
    · simpa using he.symm
    · simpa [rhombicGapPoint_im] using hrow
  apply hz
  apply (rhombicGapPoint_lattice_iff ht z).mp
  rw [hpoint]
  exact (rhombicPeriodPair t ht).lattice.neg_mem (rhombicPeriodPair t ht).ω₁_mem_lattice

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rhombicGapPoint_re_strict_of_row
