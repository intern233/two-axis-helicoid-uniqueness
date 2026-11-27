import TwoAxisHelicoid.GaussPrincipalParts
import TwoAxisHelicoid.WeierstrassAllMonotone

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate
attribute [local irreducible] thetaZeta thetaEtaExpression
set_option maxHeartbeats 1200000

theorem real_below_a_not_mem_gaussLogPoleSet {t a x : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) a) :
    (x : ℂ) ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a := by
  apply (not_mem_gaussLogPoleSet _ _ _).mpr
  refine ⟨real_not_mem_rhombic_lattice_of_pos ht hx.1 (by linarith [ha.2,hx.2]),?_,?_⟩
  · intro h
    have hn := real_not_mem_rhombic_lattice_of_pos ht (show 0 < a-x by linarith [hx.2])
      (show a-x < 2 by linarith [ha.2,hx.1])
    apply hn
    have he : ((a-x : ℝ) : ℂ) = -((x : ℂ)-(a : ℂ)) := by push_cast; ring
    rw [he]
    exact (rhombicPeriodPair t ht).lattice.neg_mem h
  · have hn := real_not_mem_rhombic_lattice_of_pos ht (show 0 < x+a by linarith [hx.1,ha.1])
      (show x+a < 2 by linarith [hx.2,ha.2])
    simpa only [Complex.ofReal_add] using hn

theorem thetaZeta_real (t x : ℝ) : (thetaZeta t x).im = 0 := by
  have h := congrArg Complex.im (thetaZeta_conj t x)
  rw [Complex.conj_ofReal,Complex.conj_im] at h
  linarith

/-- Reflection symmetry forces both coefficients in the classified Gauss
differential to be real. This uses two distinct actual values of the strictly
decreasing real Weierstrass function. -/
theorem gauss_log_coefficients_real {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1)
    {f : ℂ → ℂ} {κ β : ℂ}
    (hform : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      f z = κ*(rhombicPeriodPair t ht).weierstrassP z+β+
        thetaZeta t (z-a)-thetaZeta t (z+a))
    (hconj : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, f (conj z) = conj (f z)) :
    κ.im = 0 ∧ β.im = 0 := by
  have hr (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) a) :
      κ.im*((rhombicPeriodPair t ht).weierstrassP x).re+β.im = 0 := by
    have hn := real_below_a_not_mem_gaussLogPoleSet ht ha hx
    have hc := congrArg Complex.im (hconj x hn)
    rw [Complex.conj_ofReal,Complex.conj_im] at hc
    have hzero : (f x).im = 0 := by linarith
    rw [hform x hn,Complex.sub_im,Complex.add_im,Complex.add_im,Complex.mul_im,
      rhombic_weierstrassP_real ht x] at hzero
    have hm : (thetaZeta t ((x : ℂ)-a)).im = 0 := by
      simpa only [Complex.ofReal_sub] using thetaZeta_real t (x-a)
    have hp : (thetaZeta t ((x : ℂ)+a)).im = 0 := by
      simpa only [Complex.ofReal_add] using thetaZeta_real t (x+a)
    simpa only [hm,hp,mul_zero,zero_add,add_zero,sub_zero] using hzero
  have h₁ := hr (a/4) ⟨by linarith [ha.1],by linarith [ha.1]⟩
  have h₂ := hr (a/2) ⟨by linarith [ha.1],by linarith [ha.1]⟩
  have hwp := rhombic_weierstrassP_strictAnti_of_pos ht ht
    (show a/4 ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [ha.1],by linarith [ha.2]⟩)
    (show a/2 ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [ha.1],by linarith [ha.2]⟩)
    (show a/4 < a/2 by linarith [ha.1])
  have he : κ.im*(((rhombicPeriodPair t ht).weierstrassP ((a/4 : ℝ) : ℂ)).re-
      ((rhombicPeriodPair t ht).weierstrassP ((a/2 : ℝ) : ℂ)).re) = 0 := by
    linear_combination h₁-h₂
  have hκ : κ.im = 0 := (mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr (ne_of_gt hwp))
  exact ⟨hκ,by simpa only [hκ,zero_mul,zero_add] using h₁⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.gauss_log_coefficients_real
