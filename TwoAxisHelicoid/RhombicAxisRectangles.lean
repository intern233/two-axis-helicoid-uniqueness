import TwoAxisHelicoid.RhombicFixedLoci
import TwoAxisHelicoid.RhombicRowTranslation
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped ComplexConjugate

/-- The two open unit-width cells in a horizontal fundamental strip. -/
def rhombicAxisRectangle (a t : ℝ) : Set ℂ :=
  re ⁻¹' Ioo a (a+1) ∩ im ⁻¹' Ioo 0 t

theorem rhombicAxisRectangle_open (a t : ℝ) : IsOpen (rhombicAxisRectangle a t) :=
  (isOpen_Ioo.preimage continuous_re).inter (isOpen_Ioo.preimage continuous_im)

theorem rhombicAxisRectangle_contractible (a : ℝ) {t : ℝ} (ht : 0 < t) :
    ContractibleSpace (rhombicAxisRectangle a t) := by
  have cv : Convex ℝ (rhombicAxisRectangle a t) :=
    ((convex_Ioo a (a+1)).linear_preimage reCLM.toLinearMap).inter
      ((convex_Ioo 0 t).linear_preimage imCLM.toLinearMap)
  apply cv.contractibleSpace
  exact ⟨⟨a+1/2,t/2⟩,⟨by constructor <;> dsimp <;> linarith,
    by constructor <;> dsimp <;> linarith⟩⟩

theorem rhombic_horizontal_fixed_projection_height {t : ℝ} (ht : 0 < t) (z : ℂ) :
    rhombicHorizontalReflection ht (periodTorusProjection (rhombicPeriodPair t ht) z) =
      periodTorusProjection (rhombicPeriodPair t ht) z ↔ ∃ n : ℤ, z.im = n*t := by
  rw [rhombicHorizontalReflection_projection,periodTorusProjection_eq_iff,rhombic_mem_lattice_iff ht]
  simp only [Complex.sub_re,Complex.conj_re,sub_self,Complex.sub_im,Complex.conj_im,sub_neg_eq_add]
  constructor
  · rintro ⟨m,n,hr,hi⟩
    refine ⟨-m,?_⟩
    push_cast
    have hn : (n:ℝ) = -2*(m:ℝ) := by linarith
    rw [hn] at hi
    nlinarith
  · rintro ⟨k,hk⟩
    refine ⟨-k,2*k,?_,?_⟩
    · push_cast
      ring
    · rw [hk]
      push_cast
      ring

/-- The projection is injective on the full open strip rectangle before
cutting it into the two components. -/
theorem rhombic_open_fundamental_inj {t : ℝ} (ht : 0 < t) {z w : ℂ}
    (zx : z.re ∈ Ioo (-2:ℝ) 0) (zy : z.im ∈ Ioo 0 t)
    (wx : w.re ∈ Ioo (-2:ℝ) 0) (wy : w.im ∈ Ioo 0 t)
    (h : periodTorusProjection (rhombicPeriodPair t ht) z = periodTorusProjection (rhombicPeriodPair t ht) w) :
    z = w := by
  obtain ⟨m,n,hr,hi⟩ := (rhombic_mem_lattice_iff ht _).mp ((periodTorusProjection_eq_iff _ _ _).mp h)
  simp only [Complex.sub_re,Complex.sub_im] at hr hi
  have hn : n = 0 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · have hle : (n:ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      nlinarith [mul_le_mul_of_nonneg_right hle ht.le,zy.2,wy.1]
    · have hle : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      nlinarith [mul_le_mul_of_nonneg_right hle ht.le,zy.1,wy.2]
  subst n
  simp only [Int.cast_zero,add_zero,zero_mul] at hr hi
  have hm : (-1:ℤ) < m ∧ m < 1 := by
    have h : (-1:ℝ) < m ∧ (m:ℝ) < 1 := ⟨by linarith [wx.1,zx.2],by linarith [wx.2,zx.1]⟩
    exact_mod_cast h
  have hm' : m = 0 := by omega
  subst m
  simp only [Int.cast_zero,mul_zero] at hr
  exact Complex.ext (by linarith) (by linarith)

/-- Removing the fixed curves of the two half-turns leaves exactly the
two indicated projected open rectangles. -/
theorem rhombic_off_axes_iff_rectangle {t : ℝ} (ht : 0 < t)
    (q : PeriodTorus (rhombicPeriodPair t ht)) :
    (rhombicHorizontalReflection ht q ≠ q ∧ rhombicVerticalReflection ht q ≠ q) ↔
      q ∈ periodTorusProjection (rhombicPeriodPair t ht) '' rhombicAxisRectangle (-2) t ∪
        periodTorusProjection (rhombicPeriodPair t ht) '' rhombicAxisRectangle (-1) t := by
  let L := rhombicPeriodPair t ht
  constructor
  · rintro ⟨hh,hv⟩
    obtain ⟨z,rfl⟩ := Quotient.exists_rep q
    let w := rhombicGapPoint t z
    have hw : periodTorusProjection L w = periodTorusProjection L z := by
      have h := periodTorusProjection_add_lattice L w _ (rhombicIntegerPeriod_mem ht (rhombicGapIndex t z) (rhombicRowIndex t z))
      exact h.symm.trans (congrArg (periodTorusProjection L) (rhombicGapPoint_add_back t z))
    have hx := rhombicGapPoint_re_bounds t z
    have hy : w.im ∈ Ico 0 t := by
      rw [show w.im = (rhombicRowPoint t z).im from rhombicGapPoint_im t z]
      exact rhombicRowPoint_im_bounds ht z
    have nx (k : ℤ) : w.re ≠ k := by
      rintro he
      apply hv
      change rhombicVerticalReflection ht (periodTorusProjection L z) = periodTorusProjection L z
      rw [← hw]
      exact (rhombic_vertical_fixed_projection_iff ht w).mpr ⟨k,he⟩
    have ypos : 0 < w.im := by
      apply lt_of_le_of_ne hy.1
      intro he
      apply hh
      change rhombicHorizontalReflection ht (periodTorusProjection L z) = periodTorusProjection L z
      rw [← hw]
      exact (rhombic_horizontal_fixed_projection_height ht w).mpr ⟨0,by simpa using he.symm⟩
    have hr : (-2:ℝ) < w.re := lt_of_le_of_ne hx.1 (by simpa using (nx (-2)).symm)
    rcases lt_or_gt_of_ne (show w.re ≠ -1 by simpa using nx (-1)) with h | h
    · exact Or.inl ⟨w,⟨⟨hr,by linarith⟩,ypos,hy.2⟩,hw⟩
    · exact Or.inr ⟨w,⟨⟨h,by dsimp [w]; linarith [hx.2]⟩,ypos,hy.2⟩,hw⟩
  · intro h
    have off (a : ℤ) (w : ℂ) (hw : w ∈ rhombicAxisRectangle a t) :
        rhombicHorizontalReflection ht (periodTorusProjection L w) ≠ periodTorusProjection L w ∧
        rhombicVerticalReflection ht (periodTorusProjection L w) ≠ periodTorusProjection L w := by
      constructor
      · intro he
        obtain ⟨n,hn⟩ := (rhombic_horizontal_fixed_projection_height ht w).mp he
        have hp : 0 < (n:ℝ) := pos_of_mul_pos_left (hn ▸ hw.2.1) ht.le
        have hpos : (0:ℤ) < n := by exact_mod_cast hp
        have ha : 1 ≤ n := by omega
        have hb : (1:ℝ) ≤ n := by exact_mod_cast ha
        nlinarith [mul_le_mul_of_nonneg_right hb ht.le,hw.2.2]
      · intro he
        obtain ⟨n,hn⟩ := (rhombic_vertical_fixed_projection_iff ht w).mp he
        have ha : a < n := by exact_mod_cast (hn ▸ hw.1.1)
        have hb : n < a+1 := by exact_mod_cast (hn ▸ hw.1.2)
        omega
    rcases h with ⟨w,hw,rfl⟩ | ⟨w,hw,rfl⟩
    · exact off (-2) w (by simpa using hw)
    · exact off (-1) w (by simpa using hw)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rhombic_off_axes_iff_rectangle
