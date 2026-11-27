import TwoAxisHelicoid.DualThetaKernel
import TwoAxisHelicoid.HorizontalPeriodCentered
import TwoAxisHelicoid.FullPeriodBranch

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
attribute [local irreducible] thetaA dualThetaA

theorem dual_midline_scale {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (I*t)*((1/2:ℂ)+I*((x/t:ℝ):ℂ)) = ((-x:ℝ):ℂ)+I*((t/2:ℝ):ℂ) := by
  have hc : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  push_cast
  field_simp
  ring_nf
  simp only [I_sq]
  ring

theorem dual_midline_not_mem_lattice {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (1/2:ℂ)+I*((x/t:ℝ):ℂ) ∉ (rhombicPeriodPair (1/t) (one_div_pos.mpr ht)).lattice := by
  intro hw
  have h := (rhombic_reciprocal_mem_iff ht _).mp hw
  rw [dual_midline_scale ht x] at h
  exact rhombic_midline_not_mem ht (-x) h

theorem dualThetaA_midline {t a : ℝ} (ht : 0 < t)
    (ha : (a:ℂ) ∉ (rhombicPeriodPair t ht).lattice) (x : ℝ) :
    dualThetaA t a ((1/2:ℂ)+I*((x/t:ℝ):ℂ)) =
      thetaA t a (((-x:ℝ):ℂ)+I*((t/2:ℝ):ℂ)) := by
  have h := thetaA_reciprocal_theta ht ha (dual_midline_not_mem_lattice ht x)
  rw [dual_midline_scale ht x] at h
  exact h.symm

/-- Exact dual integral used by the manuscript's small-height certificates,
including the negative inverse-square prefactor and the exponential exp(2πiw). -/
theorem horizontal_period_dual {t a : ℝ} (ht : 0 < t)
    (ha : (a:ℂ) ∉ (rhombicPeriodPair t ht).lattice) :
    thetaHorizontalPeriod t a =
      (∫ x : ℝ in (-1/2)..(1/2), dualThetaA t a ((1/2:ℂ)+I*((x/t:ℝ):ℂ))).re := by
  rw [horizontal_period_centered ht a]
  apply congrArg Complex.re
  have he := intervalIntegral.integral_comp_neg
    (fun x : ℝ => thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ))) (a := (-1/2:ℝ)) (b := (1/2:ℝ))
  norm_num only [neg_div,neg_neg] at he
  calc
    _ = ∫ x : ℝ in (-1/2)..(1/2), thetaA t a (((-x:ℝ):ℂ)+I*((t/2:ℝ):ℂ)) := by
      simpa only [neg_div] using he.symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x _
      exact (dualThetaA_midline ht ha x).symm

theorem actualPeriodAlong_eq_dual {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    actualPeriodAlong t = (∫ x : ℝ in (-1/2)..(1/2),
      dualThetaA t (verticalA t) ((1/2:ℂ)+I*((x/t:ℝ):ℂ))).re := by
  have ha := (verticalA_spec ht).1
  exact horizontal_period_dual ht.1
    (real_not_mem_rhombic_lattice_of_pos ht.1 ha.1 (by linarith [ha.2]))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.horizontal_period_dual
#print axioms TwoAxisHelicoid.actualPeriodAlong_eq_dual
