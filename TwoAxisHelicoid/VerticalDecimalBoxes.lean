module

public import TwoAxisHelicoid.VerticalAttachmentSlope
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order

public section

namespace TwoAxisHelicoid.VerticalAttachment

def ContainsReal (interval : Box) (x : ℝ) : Prop :=
  (interval.1 : ℝ) ≤ x ∧ x ≤ (interval.2 : ℝ)

/-- Rounding both endpoints on the original decimal grid preserves enclosure. -/
theorem outward_contains_real {lo hi : ℚ} {x : ℝ}
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) : ContainsReal (outward lo hi) x := by
  have scale_pos : 0 < decimalScale := by decide +kernel
  have lower : (outward lo hi).1 ≤ lo :=
    (div_le_iff₀ scale_pos).2 (Rat.floor_le _)
  have upper : hi ≤ (outward lo hi).2 :=
    (le_div_iff₀ scale_pos).2 Rat.le_ceil
  exact ⟨(Rat.cast_le.mpr lower).trans hlo, hhi.trans (Rat.cast_le.mpr upper)⟩

theorem boxAdd_contains {a b : Box} {x y : ℝ} (ha : ContainsReal a x) (hb : ContainsReal b y) :
    ContainsReal (boxAdd a b) (x+y) := by
  apply outward_contains_real
  · simpa only [Rat.cast_add] using add_le_add ha.1 hb.1
  · simpa only [Rat.cast_add] using add_le_add ha.2 hb.2

theorem boxNeg_contains {a : Box} {x : ℝ} (ha : ContainsReal a x) :
    ContainsReal (boxNeg a) (-x) := by
  simpa only [ContainsReal, boxNeg, Rat.cast_neg] using And.intro (neg_le_neg ha.2) (neg_le_neg ha.1)

private theorem scale_interval {l x u : ℝ} (hl : l ≤ x) (hu : x ≤ u) (c : ℝ) :
    min (l*c) (u*c) ≤ x*c ∧ x*c ≤ max (l*c) (u*c) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hl hc),
      (mul_le_mul_of_nonneg_right hu hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hu hc),
      (mul_le_mul_of_nonpos_right hl hc).trans (le_max_left _ _)⟩

theorem boxMul_contains {a b : Box} {x y : ℝ} (ha : ContainsReal a x) (hb : ContainsReal b y) :
    ContainsReal (boxMul a b) (x*y) := by
  have bounds := scale_interval ha.1 ha.2 y
  have left := scale_interval hb.1 hb.2 (a.1 : ℝ)
  have right := scale_interval hb.1 hb.2 (a.2 : ℝ)
  apply outward_contains_real
  · simp only [Rat.cast_min, Rat.cast_mul]
    refine (min_le_min ?_ ?_).trans bounds.1
    · simpa only [mul_comm (b.1 : ℝ), mul_comm (b.2 : ℝ), mul_comm y] using left.1
    · simpa only [mul_comm (b.1 : ℝ), mul_comm (b.2 : ℝ), mul_comm y] using right.1
  · simp only [Rat.cast_max, Rat.cast_mul]
    refine bounds.2.trans (max_le_max ?_ ?_)
    · simpa only [mul_comm (b.1 : ℝ), mul_comm (b.2 : ℝ), mul_comm y] using left.2
    · simpa only [mul_comm (b.1 : ℝ), mul_comm (b.2 : ℝ), mul_comm y] using right.2

theorem boxScale_contains {a : Box} {x : ℝ} (ha : ContainsReal a x) (k : ℚ) :
    ContainsReal (boxScale a k) (x*(k : ℝ)) :=
  boxMul_contains ha ⟨le_rfl, le_rfl⟩

theorem boxDiv_contains {a b : Box} {x y : ℝ} (ha : ContainsReal a x) (hb : ContainsReal b y)
    (hpos : 0 < b.1) : ContainsReal (boxDiv a b) (x/y) := by
  have lo : 0 < (b.1 : ℝ) := by exact_mod_cast hpos
  have hy := lo.trans_le hb.1
  rw [div_eq_mul_one_div]
  apply boxMul_contains ha
  constructor
  · simpa only [Rat.cast_div, Rat.cast_one] using one_div_le_one_div_of_le hy hb.2
  · simpa only [Rat.cast_div, Rat.cast_one] using one_div_le_one_div_of_le lo hb.1

end TwoAxisHelicoid.VerticalAttachment

#print axioms TwoAxisHelicoid.VerticalAttachment.boxMul_contains
#print axioms TwoAxisHelicoid.VerticalAttachment.boxDiv_contains
