import TwoAxisHelicoid.SigmaAllIdentities
import TwoAxisHelicoid.WeierstrassScaling
import TwoAxisHelicoid.SigmaAllPositive
import Mathlib.Analysis.Calculus.MeanValue

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaZeta

theorem reciprocal_not_mem_lattice {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    z/(I*t) ∉ (rhombicPeriodPair (1/t) (one_div_pos.mpr ht)).lattice := by
  have hi : (I*t:ℂ) ≠ 0 := mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne')
  intro h
  have h' := (rhombic_reciprocal_mem_iff ht _).mp h
  rw [mul_div_cancel₀ _ hi] at h'
  exact hz h'

theorem thetaZeta_reciprocal {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    thetaZeta t z = thetaZeta (1/t) (z/(I*t))/(I*t) := by
  let L := rhombicPeriodPair t ht
  let D : ℂ → ℂ := fun w => thetaZeta t w-thetaZeta (1/t) (w/(I*t))/(I*t)
  have htinv := one_div_pos.mpr ht
  have hi : (I*t:ℂ) ≠ 0 := mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne')
  have hd (w : ℂ) (hw : w ∉ L.lattice) : HasDerivAt D 0 w := by
    have hs := ((thetaZeta_hasDerivAt_of_pos htinv htinv (reciprocal_not_mem_lattice ht hw)).comp
      (h := fun v : ℂ => v/(I*t)) w ((hasDerivAt_id w).div_const (I*t))).div_const (I*t)
    have h := (thetaZeta_hasDerivAt_of_pos ht ht hw).sub hs
    convert h using 1
    · rfl
    · rw [rhombic_weierstrassP_reciprocal ht w]
      field_simp
      ring_nf
      simp only [I_sq]
      ring
  have hconn : IsPreconnected (L.lattice:Set ℂ)ᶜ := by
    refine (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) ?_).2
    exact countable_of_Lindelof_of_discrete (X := L.lattice)
  have hneg : -z ∉ L.lattice := by simpa using hz
  have hc := L.isClosed_lattice.isOpen_compl.is_const_of_deriv_eq_zero hconn
    (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hd w hw).deriv) hz hneg
  have he : D (-z) = -D z := by
    unfold D
    rw [thetaZeta_neg,neg_div,thetaZeta_neg]
    ring
  rw [he] at hc
  change thetaZeta t z-thetaZeta (1/t) (z/(I*t))/(I*t) =
    -(thetaZeta t z-thetaZeta (1/t) (z/(I*t))/(I*t)) at hc
  linear_combination (1/2:ℂ)*hc

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaZeta_reciprocal
