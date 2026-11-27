import TwoAxisHelicoid.PdfComplexGrid
import TwoAxisHelicoid.PdfVerticalGridSound
import Mathlib.Analysis.Complex.Basic

namespace TwoAxisHelicoid.PdfVertical

theorem Grid.contains_squared {a : Grid} {x : ℝ} (h : a.Contains x) : a.squared.Contains (x^2) := by
  intro ok
  obtain ⟨l,u⟩ := Grid.contains_mul h h ok
  change (((max (a.mul a).lo 0:ℤ)):ℝ)≤_ ∧ _≤((a.mul a).hi:ℝ)
  rw [Int.cast_max,Int.cast_zero,pow_two]
  exact ⟨max_le l (mul_nonneg Grid.real_denom_pos.le (mul_self_nonneg x)),u⟩

theorem Grid.contains_widen {a : Grid} {x y : ℝ} (h : a.Contains x) {r : ℤ}
    (err : |(Grid.denom:ℝ)*(y-x)|≤(r:ℝ)) : (a.widen r).Contains y := by
  intro valid
  obtain ⟨lo,hi⟩ := h valid
  obtain ⟨l,u⟩ := abs_le.mp err
  change ((a.lo-r:ℤ):ℝ)≤_ ∧ _≤((a.hi+r:ℤ):ℝ)
  push_cast
  constructor <;> linarith only [lo,hi,l,u]

namespace CGrid
open Grid

def Contains (a : CGrid) (z : ℂ) : Prop := a.re.Contains z.re ∧ a.im.Contains z.im

theorem contains_real {a : Grid} {x : ℝ} (h : a.Contains x) : (real a).Contains (x:ℂ) :=
  ⟨h,by simpa only [real,Complex.ofReal_im,Int.cast_zero] using Grid.contains_int 0⟩

theorem contains_imaginary {a : Grid} {y : ℝ} (h : a.Contains y) : (imaginary a).Contains (y*Complex.I) := by
  change (Grid.ofInt 0).Contains _ ∧ a.Contains _
  simp only [Complex.mul_I_re,Complex.ofReal_im,neg_zero,Complex.mul_I_im,Complex.ofReal_re]
  exact ⟨by simpa using Grid.contains_int 0,h⟩

theorem contains_ofInt (n : ℤ) : (ofInt n).Contains (n:ℂ) := by
  simpa only [ofInt,Complex.ofReal_intCast] using (contains_real (Grid.contains_int n))

theorem contains_add {a b : CGrid} {z w : ℂ} (h : a.Contains z) (k : b.Contains w) :
    (a.add b).Contains (z+w) := ⟨Grid.contains_add h.1 k.1,Grid.contains_add h.2 k.2⟩

theorem contains_neg {a : CGrid} {z : ℂ} (h : a.Contains z) :
    a.neg.Contains (-z) := ⟨Grid.contains_neg h.1,Grid.contains_neg h.2⟩

theorem contains_sub {a b : CGrid} {z w : ℂ} (h : a.Contains z) (k : b.Contains w) :
    (a.sub b).Contains (z-w) := by simpa only [sub,sub_eq_add_neg] using contains_add h (contains_neg k)

theorem contains_mul {a b : CGrid} {z w : ℂ} (h : a.Contains z) (k : b.Contains w) :
    (a.mul b).Contains (z*w) :=
  ⟨Grid.contains_sub (Grid.contains_mul h.1 k.1) (Grid.contains_mul h.2 k.2),
    Grid.contains_add (Grid.contains_mul h.1 k.2) (Grid.contains_mul h.2 k.1)⟩

theorem contains_scale {a : Grid} {s : ℝ} {b : CGrid} {z : ℂ} (h : a.Contains s) (k : b.Contains z) :
    (scale a b).Contains ((s:ℂ)*z) := by
  change (a.mul b.re).Contains _ ∧ (a.mul b.im).Contains _
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,zero_mul,sub_zero,add_zero]
  exact ⟨Grid.contains_mul h k.1,Grid.contains_mul h k.2⟩

theorem contains_rot {a : CGrid} {z : ℂ} (h : a.Contains z) :
    a.rot.Contains (z*Complex.I) := by
  change a.im.neg.Contains _ ∧ a.re.Contains _
  rw [Complex.mul_I_re,Complex.mul_I_im]
  exact ⟨Grid.contains_neg h.2,h.1⟩

theorem contains_inv {a : CGrid} {z : ℂ} (h : a.Contains z) : a.inv.Contains z⁻¹ := by
  have hd : (a.re.squared.add a.im.squared).Contains (Complex.normSq z) := by
    simpa only [Complex.normSq_apply,pow_two] using Grid.contains_add (Grid.contains_squared h.1) (Grid.contains_squared h.2)
  change (a.re.divPos _).Contains _ ∧ (a.im.neg.divPos _).Contains _
  rw [Complex.inv_re,Complex.inv_im]
  exact ⟨Grid.contains_div h.1 hd,Grid.contains_div (Grid.contains_neg h.2) hd⟩

theorem contains_div {a b : CGrid} {z w : ℂ} (h : a.Contains z) (k : b.Contains w) :
    (a.div b).Contains (z/w) := by simpa only [div,div_eq_mul_inv] using contains_mul h (contains_inv k)

theorem contains_divNat {a : CGrid} {z : ℂ} (h : a.Contains z) (n : ℕ) :
    (a.divNat n).Contains (z/(n:ℂ)) := by
  change (a.re.divNat n).Contains _ ∧ (a.im.divNat n).Contains _
  rw [← Complex.ofReal_natCast,Complex.div_ofReal_re,Complex.div_ofReal_im]
  exact ⟨Grid.contains_divNat h.1,Grid.contains_divNat h.2⟩

theorem contains_widen {a : CGrid} {z w : ℂ} (h : a.Contains z) {r : ℤ}
    (er : |(Grid.denom:ℝ)*(w.re-z.re)|≤(r:ℝ)) (ei : |(Grid.denom:ℝ)*(w.im-z.im)|≤(r:ℝ)) :
    (a.widen r).Contains w := ⟨Grid.contains_widen h.1 er,Grid.contains_widen h.2 ei⟩

end CGrid
end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.CGrid.contains_div
