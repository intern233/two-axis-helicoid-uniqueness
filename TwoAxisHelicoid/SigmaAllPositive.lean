import TwoAxisHelicoid.SigmaAllIdentities
import TwoAxisHelicoid.SigmaRealPositive
import TwoAxisHelicoid.RhombicRegularPaths
import TwoAxisHelicoid.PositiveFromSimpleZero

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaSigma

theorem real_not_mem_rhombic_lattice_of_pos {t : ℝ} (ht : 0 < t) {x : ℝ}
    (hx : 0 < x) (hx2 : x < 2) : (x:ℂ) ∉ (rhombicPeriodPair t ht).lattice := by
  intro hz
  obtain ⟨m,n,hr,hi⟩ := (rhombic_mem_lattice_iff ht _).mp hz
  simp only [Complex.ofReal_re,Complex.ofReal_im] at hr hi
  have hn : (n:ℝ) = 0 := (mul_eq_zero.mp hi.symm).resolve_right ht.ne'
  rw [hn,add_zero] at hr
  have hm0 : (0:ℤ) < m := by exact_mod_cast (show (0:ℝ) < m by linarith)
  have hm1 : m < (1:ℤ) := by exact_mod_cast (show (m:ℝ) < 1 by linarith)
  omega

theorem thetaSigma_re_ne_zero_of_pos {t : ℝ} (ht : 0 < t) {x : ℝ}
    (hx : 0 < x) (hx2 : x < 2) : (thetaSigma t x).re ≠ 0 := by
  intro h
  have hz : thetaSigma t x = 0 := by
    apply Complex.ext
    · exact h
    · exact thetaSigma_real t x
  exact real_not_mem_rhombic_lattice_of_pos ht hx hx2
    ((thetaSigma_zero_iff_lattice_of_pos ht ht x).mp hz)

theorem thetaSigma_re_pos_of_pos {t : ℝ} (ht : 0 < t) {x : ℝ}
    (hx : 0 < x) (hx2 : x < 2) : 0 < (thetaSigma t x).re := by
  have hc : Continuous (fun y : ℝ => (thetaSigma t y).re) := by
    have hf : Continuous (thetaSigma t) :=
      (show Differentiable ℂ (thetaSigma t) from fun z => (thetaSigma_hasDerivAt ht z).differentiableAt).continuous
    exact Complex.continuous_re.comp (hf.comp Complex.continuous_ofReal)
  have hd : HasDerivAt (fun y : ℝ => (thetaSigma t y).re) 1 0 :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (thetaSigma_hasDerivAt_zero_of_pos ht).comp_ofReal
  exact positive_on_interval_of_simple_zero hc.continuousOn
    (by simp only [Complex.ofReal_zero,thetaSigma_zero,Complex.zero_re]) hd (by norm_num)
    (fun y hy => thetaSigma_re_ne_zero_of_pos ht hy.1 hy.2) ⟨hx,hx2⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaSigma_re_pos_of_pos
