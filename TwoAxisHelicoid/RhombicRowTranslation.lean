import TwoAxisHelicoid.RhombicRowCoordinates

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 1000000

noncomputable def rhombicIntegerPeriod (t : ℝ) (m n : ℤ) : ℂ :=
  (m : ℂ)*2+(n : ℂ)*(1+I*t)

theorem rhombicIntegerPeriod_mem {t : ℝ} (ht : 0 < t) (m n : ℤ) :
    rhombicIntegerPeriod t m n ∈ (rhombicPeriodPair t ht).lattice :=
  PeriodPair.mem_lattice.mpr ⟨m,n,rfl⟩

theorem rhombicRowIndex_add_integer_period {t : ℝ} (ht : 0 < t) (z : ℂ) (m n : ℤ) :
    rhombicRowIndex t (z+rhombicIntegerPeriod t m n) = rhombicRowIndex t z+n := by
  unfold rhombicRowIndex
  have he : (z+rhombicIntegerPeriod t m n).im/t = z.im/t+(n : ℝ) := by
    simp [rhombicIntegerPeriod,Complex.mul_im]
    field_simp
  rw [he,Int.floor_add_intCast]

theorem rhombicRowPoint_add_integer_period {t : ℝ} (ht : 0 < t) (z : ℂ) (m n : ℤ) :
    rhombicRowPoint t (z+rhombicIntegerPeriod t m n) = rhombicRowPoint t z+(m : ℂ)*2 := by
  unfold rhombicRowPoint
  rw [rhombicRowIndex_add_integer_period ht z m n]
  unfold rhombicIntegerPeriod
  push_cast
  ring

theorem rhombicGapIndex_add_integer_period {t : ℝ} (ht : 0 < t) (z : ℂ) (m n : ℤ) :
    rhombicGapIndex t (z+rhombicIntegerPeriod t m n) = rhombicGapIndex t z+m := by
  unfold rhombicGapIndex
  rw [rhombicRowPoint_add_integer_period ht z m n]
  have he : (rhombicRowPoint t z+(m : ℂ)*2).re/2 = (rhombicRowPoint t z).re/2+(m : ℝ) := by
    simp [Complex.mul_re]
    ring
  rw [he,Int.floor_add_intCast]
  omega

theorem rhombicGapPoint_add_integer_period {t : ℝ} (ht : 0 < t) (z : ℂ) (m n : ℤ) :
    rhombicGapPoint t (z+rhombicIntegerPeriod t m n) = rhombicGapPoint t z := by
  unfold rhombicGapPoint
  rw [rhombicRowPoint_add_integer_period ht z m n,rhombicGapIndex_add_integer_period ht z m n]
  push_cast
  ring

theorem rhombicRowPoint_add_back (t : ℝ) (z : ℂ) :
    rhombicRowPoint t z+rhombicIntegerPeriod t 0 (rhombicRowIndex t z) = z := by
  simp [rhombicRowPoint,rhombicIntegerPeriod]

theorem rhombicGapPoint_add_back (t : ℝ) (z : ℂ) :
    rhombicGapPoint t z+rhombicIntegerPeriod t (rhombicGapIndex t z) (rhombicRowIndex t z) = z := by
  unfold rhombicGapPoint rhombicRowPoint rhombicIntegerPeriod
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rhombicGapPoint_add_integer_period
