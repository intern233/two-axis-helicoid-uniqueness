import TwoAxisHelicoid.RhombicPrimitiveMatching
import TwoAxisHelicoid.RhombicRowTranslation

namespace TwoAxisHelicoid
open Complex Set
set_option maxHeartbeats 1200000

/-- An explicit real primitive on the lattice complement. Points between
rows use the horizontal-strip primitive; points on a row use the adjoining
pole-free rectangle. The two actual closing periods will prove the gluing. -/
noncomputable def rhombicGlobalRealPrimitive (t : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  if 0 < (rhombicRowPoint t z).im then (rhombicWedgePrimitive t f (rhombicRowPoint t z)).re
  else (rhombicWedgePrimitive t f (rhombicGapPoint t z)).re

theorem rhombicWedgePrimitive_horizontal_integer_period {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : ∀ z ∉ (rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z)
    (hp : ∀ z ω, ω ∈ (rhombicPeriodPair t ht).lattice → f (z+ω) = f z)
    (hd : (rhombicDownPeriod t f).re = 0) (hu : (rhombicUpPeriod t f).re = 0)
    {z : ℂ} (hz : z ∈ complexHorizontalStrip 0 t) (m : ℤ) :
    (rhombicWedgePrimitive t f (z+(m : ℂ)*2)).re = (rhombicWedgePrimitive t f z).re := by
  classical
  let F : ℂ → ℝ := fun z => if z ∈ complexHorizontalStrip 0 t then (rhombicWedgePrimitive t f z).re else 0
  have hF : Function.Periodic F 2 := by
    intro w
    have hm : w+2 ∈ complexHorizontalStrip 0 t ↔ w ∈ complexHorizontalStrip 0 t := by
      simp [complexHorizontalStrip]
    dsimp only [F]
    rw [hm]
    by_cases hw : w ∈ complexHorizontalStrip 0 t
    · simp only [ite_eq_left hw]
      exact rhombicWedgePrimitive_horizontal_real_period ht hf hp hd hu hw
    · simp only [ite_eq_right hw]
  have hzm : z+(m : ℂ)*2 ∈ complexHorizontalStrip 0 t := by
    simpa [complexHorizontalStrip,Complex.mul_im] using hz
  have he := hF.zsmul m z
  simp only [zsmul_eq_mul,F,ite_eq_left hz,ite_eq_left hzm] at he
  exact he

theorem rhombicGlobalRealPrimitive_add_integer_period {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : ∀ z ∉ (rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z)
    (hp : ∀ z ω, ω ∈ (rhombicPeriodPair t ht).lattice → f (z+ω) = f z)
    (hd : (rhombicDownPeriod t f).re = 0) (hu : (rhombicUpPeriod t f).re = 0)
    (z : ℂ) (m n : ℤ) :
    rhombicGlobalRealPrimitive t f (z+rhombicIntegerPeriod t m n) = rhombicGlobalRealPrimitive t f z := by
  unfold rhombicGlobalRealPrimitive
  rw [rhombicRowPoint_add_integer_period ht z m n,rhombicGapPoint_add_integer_period ht z m n]
  have he : (rhombicRowPoint t z+(m : ℂ)*2).im = (rhombicRowPoint t z).im := by simp
  rw [he]
  by_cases hpos : 0 < (rhombicRowPoint t z).im
  · simp only [ite_eq_left hpos]
    exact rhombicWedgePrimitive_horizontal_integer_period ht hf hp hd hu
      ⟨hpos,(rhombicRowPoint_im_bounds ht z).2⟩ m
  · simp only [ite_eq_right hpos]

theorem rhombicGlobalRealPrimitive_add_lattice {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : ∀ z ∉ (rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z)
    (hp : ∀ z ω, ω ∈ (rhombicPeriodPair t ht).lattice → f (z+ω) = f z)
    (hd : (rhombicDownPeriod t f).re = 0) (hu : (rhombicUpPeriod t f).re = 0)
    (z ω : ℂ) (hω : ω ∈ (rhombicPeriodPair t ht).lattice) :
    rhombicGlobalRealPrimitive t f (z+ω) = rhombicGlobalRealPrimitive t f z := by
  obtain ⟨m,n,he⟩ := PeriodPair.mem_lattice.mp hω
  have he' : rhombicIntegerPeriod t m n = ω := he
  rw [← he']
  exact rhombicGlobalRealPrimitive_add_integer_period ht hf hp hd hu z m n

theorem rhombicGlobalRealPrimitive_on_strip {t : ℝ} (ht : 0 < t) (f : ℂ → ℂ) {z : ℂ}
    (hz : z ∈ complexHorizontalStrip 0 t) :
    rhombicGlobalRealPrimitive t f z = (rhombicWedgePrimitive t f z).re := by
  have hi : rhombicRowIndex t z = 0 := (rhombicRowIndex_eq_iff ht z 0).mpr
    (by simpa only [Int.cast_zero,zero_mul,zero_add,one_mul] using And.intro hz.1.le hz.2)
  have he : rhombicRowPoint t z = z := by simp [rhombicRowPoint,hi]
  unfold rhombicGlobalRealPrimitive
  rw [he,ite_eq_left hz.1]

theorem rhombicGlobalRealPrimitive_on_bridge {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : ∀ z ∉ (rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z)
    (hp : ∀ z ω, ω ∈ (rhombicPeriodPair t ht).lattice → f (z+ω) = f z)
    (hu : (rhombicUpPeriod t f).re = 0)
    {z : ℂ} (hz : z ∈ complexOpenRect (-2) 0 (-t) t) :
    rhombicGlobalRealPrimitive t f z = (rhombicWedgePrimitive t f z).re := by
  rcases lt_trichotomy 0 z.im with hpos | heq | hneg
  · exact rhombicGlobalRealPrimitive_on_strip ht f ⟨hpos,hz.2.2⟩
  · have hi : rhombicRowIndex t z = 0 := (rhombicRowIndex_eq_iff ht z 0).mpr
      (by simp only [Int.cast_zero,zero_mul,zero_add,one_mul]; constructor <;> linarith)
    have hr : rhombicRowPoint t z = z := by simp [rhombicRowPoint,hi]
    have hm : rhombicGapIndex t z = 0 := by
      unfold rhombicGapIndex
      rw [hr]
      have hfloor : ⌊z.re/2⌋ = (-1 : ℤ) := Int.floor_eq_iff.mpr (by
        norm_num
        constructor <;> linarith [hz.1.1,hz.1.2])
      rw [hfloor]
      norm_num
    have hb : rhombicGapPoint t z = z := by simp [rhombicGapPoint,hr,hm]
    unfold rhombicGlobalRealPrimitive
    rw [hr,hb,ite_eq_right (by linarith : ¬ 0 < z.im)]
  · have hi : rhombicRowIndex t z = -1 := (rhombicRowIndex_eq_iff ht z (-1)).mpr (by
      norm_num
      exact ⟨hz.2.1.le,hneg⟩)
    have hr : rhombicRowPoint t z = z+(1+I*t) := by
      simp [rhombicRowPoint,hi]
      ring
    have hpos : 0 < (rhombicRowPoint t z).im := by
      rw [hr]
      simp only [Complex.add_im,Complex.one_im,Complex.mul_im,Complex.I_re,Complex.I_im,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add]
      linarith [hz.2.1]
    unfold rhombicGlobalRealPrimitive
    rw [ite_eq_left hpos,hr]
    exact rhombicWedgePrimitive_lower_real_matching ht hf hp hu ⟨hz.1,⟨hz.2.1,hneg⟩⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rhombicGlobalRealPrimitive_add_lattice
#print axioms TwoAxisHelicoid.rhombicGlobalRealPrimitive_on_bridge
