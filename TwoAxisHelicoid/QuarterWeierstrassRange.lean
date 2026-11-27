import TwoAxisHelicoid.RhombicQuarterHeight
import TwoAxisHelicoid.RhombicCenteredRectangle
import TwoAxisHelicoid.WeierstrassSurjectivity
import TwoAxisHelicoid.AxisCoefficientPositive

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

/-- The first parameter rectangle covers the entire lower half-plane
under ℘. Two points in this rectangle have the same value precisely
when they agree or are exchanged by the central half-turn. -/
theorem rhombic_quarter_weierstrass_image_and_fibers {t : ℝ} (ht : 0<t) :
    let L := rhombicPeriodPair t ht
    let U := complexOpenRect 0 1 0 t
    L.weierstrassP '' U={u | u.im<0} ∧
    ∀ z∈U, ∀ w∈U, L.weierstrassP z=L.weierstrassP w ↔ z=w ∨ z+w=1+I*t := by
  intro L U
  have neg (z : ℂ) (h : z∈U) : (L.weierstrassP z).im<0 := by
    have n := rhombic_weierstrassP_quarter_im_neg ht h.1 h.2
    rwa [show (z.re:ℂ)+I*z.im=z by apply Complex.ext <;> simp] at n
  constructor
  · apply Subset.antisymm (image_subset_iff.mpr (by intro z hz; exact neg z hz))
    intro u hu
    change u.im<0 at hu
    obtain ⟨z,_,eq⟩ := weierstrassP_attains_every_finite_value L u
    obtain ⟨x,y,hx,hy,hp⟩ := rhombic_centered_rectangle_rep ht z
    let w := (x:ℂ)+I*y
    have val : L.weierstrassP w=u := by
      have e := L.weierstrassP_add_coe w (⟨z-w,hp⟩:L.lattice)
      rw [show w+((⟨z-w,hp⟩:L.lattice):ℂ)=z by change w+(z-w)=z; abel] at e
      exact e.symm.trans eq
    have bad : (L.weierstrassP w).im<0 := val.symm ▸ hu
    have posy : 0<y := hy.1.lt_of_ne (by
      rintro rfl
      simp [w,L,rhombic_weierstrassP_real] at bad)
    have neX : x≠-1 := by
      rintro rfl
      have e := L.weierstrassP_add_coe w (⟨1+I*t,L.ω₂_mem_lattice⟩:L.lattice)
      have alg : w+((⟨1+I*t,L.ω₂_mem_lattice⟩:L.lattice):ℂ)=I*(y+t:ℝ) := by dsimp [w]; push_cast; ring
      rw [alg] at e
      rw [← e] at bad
      exact (rhombic_weierstrassP_imaginary_real ht (y+t)).not_lt bad
    have posx : 0<x := by
      by_contra! nonpos
      rcases nonpos.eq_or_lt with zero | minus
      · subst x
        simp [w,L,rhombic_weierstrassP_imaginary_real] at bad
      · have inside : -conj w∈U := by
          refine ⟨?_,?_⟩
          · simp only [w,neg_re,conj_re,add_re,ofReal_re,I_mul_re,ofReal_im,neg_zero,add_zero]
            exact ⟨neg_pos.mpr minus,by linarith [lt_of_le_of_ne hx.1 neX.symm]⟩
          · simpa [w] using (show y∈Ioo 0 t from ⟨posy,hy.2⟩)
        have h := neg _ inside
        rw [L.weierstrassP_neg,rhombic_weierstrassP_conj,conj_im] at h
        linarith
    exact ⟨w,⟨by simpa [w] using (show x∈Ioo (0:ℝ) 1 from ⟨posx,hx.2⟩),
      by simpa [w] using (show y∈Ioo 0 t from ⟨posy,hy.2⟩)⟩,val⟩
  · intro z hz w hw
    have extend {v : ℂ} (h : v∈U) : v.re∈Ioo (-1:ℝ) 1 := ⟨by linarith [h.1.1],h.1.2⟩
    have off {v : ℂ} (h : v∈U) : v∉L.lattice := rhombic_horizontal_strip_not_mem ht h.2
    rw [rhombic_weierstrassP_eq_iff ht (off hw) (off hz)]
    constructor
    · rintro (diff | sum)
      · exact Or.inl (rhombic_centered_open_rectangle_inj ht (extend hz) hz.2 (extend hw) hw.2 diff)
      · let v : ℂ := 1+I*t-w
        have vIn : v∈U := by
          constructor
          · simp only [v,sub_re,add_re,one_re,I_mul_re,ofReal_im,neg_zero,add_zero,mem_Ioo]
            constructor <;> linarith [hw.1.1,hw.1.2]
          · simp only [v,sub_im,add_im,one_im,I_mul_im,ofReal_re,zero_add,mem_Ioo]
            constructor <;> linarith [hw.2.1,hw.2.2]
        have p : z-v∈L.lattice := by
          rw [show z-v=z+w-(1+I*t) by dsimp [v]; ring]
          exact L.lattice.sub_mem sum L.ω₂_mem_lattice
        have e := rhombic_centered_open_rectangle_inj ht (extend hz) hz.2 (extend vIn) vIn.2 p
        right
        rw [e]
        exact sub_add_cancel _ _
    · rintro (rfl|eq)
      · exact Or.inl (by simp)
      · exact Or.inr (eq ▸ L.ω₂_mem_lattice)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rhombic_quarter_weierstrass_image_and_fibers
