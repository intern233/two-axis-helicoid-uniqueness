import TwoAxisHelicoid.RhombicAxisRectangles

namespace TwoAxisHelicoid
open Complex Set

/-- Each lattice class has a representative in the half-open rectangle
of width two centered on the imaginary axis. -/
theorem rhombic_centered_rectangle_rep {t : ℝ} (ht : 0<t) (z : ℂ) :
    ∃ (x y : ℝ), x∈Ico (-1:ℝ) 1 ∧ y∈Ico 0 t ∧
      z-((x:ℂ)+I*y)∈(rhombicPeriodPair t ht).lattice := by
  let u := z-1
  let v := rhombicGapPoint t u
  let p := rhombicIntegerPeriod t (rhombicGapIndex t u) (rhombicRowIndex t u)
  have ep : v+p=z-1 := rhombicGapPoint_add_back t u
  have re := rhombicGapPoint_re_bounds t u
  have im := rhombicRowPoint_im_bounds ht u
  rw [← rhombicGapPoint_im] at im
  change -2≤v.re ∧ v.re<0 at re
  refine ⟨v.re+1,v.im,⟨by linarith [re.1],by linarith [re.2]⟩,im,?_⟩
  have e : ((v.re+1:ℝ):ℂ)+I*v.im=v+1 := by apply Complex.ext <;> simp
  rw [e,show z-(v+1)=p by linear_combination -ep]
  exact rhombicIntegerPeriod_mem ht _ _

/-- Two points of the centered open rectangle represent the same
period class only when both coordinates agree. -/
theorem rhombic_centered_open_rectangle_inj {t : ℝ} (ht : 0<t) {z w : ℂ}
    (zx : z.re∈Ioo (-1:ℝ) 1) (zy : z.im∈Ioo 0 t)
    (wx : w.re∈Ioo (-1:ℝ) 1) (wy : w.im∈Ioo 0 t)
    (lattice : z-w∈(rhombicPeriodPair t ht).lattice) : z=w := by
  have bound {u : ℂ} (h : u.re∈Ioo (-1:ℝ) 1) : (u-1).re∈Ioo (-2:ℝ) 0 := by
    simp only [sub_re,one_re,mem_Ioo]
    constructor <;> linarith [h.1,h.2]
  have eq := rhombic_open_fundamental_inj ht (bound zx) (by simpa using zy)
    (bound wx) (by simpa using wy) ((periodTorusProjection_eq_iff _ _ _).mpr (by
      rw [show (w-1)-(z-1)= -(z-w) by ring]
      exact (rhombicPeriodPair t ht).lattice.neg_mem lattice))
  linear_combination eq

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rhombic_centered_open_rectangle_inj
