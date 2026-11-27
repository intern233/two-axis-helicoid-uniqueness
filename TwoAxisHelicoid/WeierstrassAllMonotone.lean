import TwoAxisHelicoid.SigmaAllPositive
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaSigma thetaG

theorem rhombic_weierstrassP_derivative_real_neg_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t)
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    ((rhombicPeriodPair t ht0).derivWeierstrassP x).re < 0 := by
  have hn := real_not_mem_rhombic_lattice_of_pos ht0 hx (by linarith : x < 2)
  have he (y : ℝ) : thetaSigma t y = ((thetaSigma t y).re:ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using thetaSigma_real t y
  have he2 : (2:ℂ)*(x:ℂ) = ((2*x:ℝ):ℂ) := by push_cast; rfl
  rw [rhombic_weierstrassP_derivative_sigma_of_pos ht ht0 hn,he2,he (2*x),he x]
  simp only [← Complex.ofReal_pow,← Complex.ofReal_neg,← Complex.ofReal_div,Complex.ofReal_re]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (thetaSigma_re_pos_of_pos ht (by linarith) (by linarith)))
    (pow_pos (thetaSigma_re_pos_of_pos ht hx (by linarith)) 4)

theorem rhombic_weierstrassP_real_hasDerivAt_of_pos {t : ℝ} (_ht : 0 < t) (ht0 : 0 < t)
    {x : ℝ} (hx : 0 < x) (hx2 : x < 2) :
    HasDerivAt (fun y : ℝ => ((rhombicPeriodPair t ht0).weierstrassP y).re)
      ((rhombicPeriodPair t ht0).derivWeierstrassP x).re x := by
  have hd := (rhombic_weierstrassP_hasDerivAt ht0 (real_not_mem_rhombic_lattice_of_pos ht0 hx hx2)).comp_ofReal
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd

theorem rhombic_weierstrassP_strictAnti_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) :
    StrictAntiOn (fun x : ℝ => ((rhombicPeriodPair t ht0).weierstrassP x).re) (Ioo 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
  · intro x hx
    exact (rhombic_weierstrassP_real_hasDerivAt_of_pos ht ht0 hx.1 (by linarith [hx.2])).continuousAt.continuousWithinAt
  · intro x hx
    have hc := interior_subset hx
    rw [(rhombic_weierstrassP_real_hasDerivAt_of_pos ht ht0 hc.1 (by linarith [hc.2])).deriv]
    exact rhombic_weierstrassP_derivative_real_neg_of_pos ht ht0 hc.1 hc.2

theorem thetaG_strictAnti_unit_of_pos {t : ℝ} (ht : 0 < t) :
    StrictAntiOn (fun x : ℝ => (thetaG t x).re) (Ioo 0 1) := by
  have ht0 : 0 < t := by linarith
  intro x hx y hy hxy
  change (thetaG t y).re < (thetaG t x).re
  rw [thetaG_eq_weierstrassP_of_pos ht ht0 x (real_not_mem_rhombic_lattice_of_pos ht0 hx.1 (by linarith [hx.2])),
    thetaG_eq_weierstrassP_of_pos ht ht0 y (real_not_mem_rhombic_lattice_of_pos ht0 hy.1 (by linarith [hy.2]))]
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re]
  have h := rhombic_weierstrassP_strictAnti_of_pos ht ht0 hx hy hxy
  dsimp only at h
  linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rhombic_weierstrassP_strictAnti_of_pos
#print axioms TwoAxisHelicoid.thetaG_strictAnti_unit_of_pos
