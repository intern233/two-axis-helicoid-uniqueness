import TwoAxisHelicoid.OriginalPeriodRegularity
import TwoAxisHelicoid.WeightedIntegrationByParts

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped Interval
attribute [local irreducible] thetaA thetaW

theorem thetaW_original_endpoints {t : ℝ} (ht : 0 < t) :
    thetaW t (originalPeriodPath t 1) =
      thetaW t (originalPeriodPath t (-1))+(Real.pi : ℂ)*I := by
  have hn := rhombic_open_rectangle_not_mem ht
    (originalPeriodPath_mem_rectangle ht (by norm_num : (1 : ℝ) ∈ Icc (-1) 1))
  have hq := thetaZeta_add_half_of_pos ht ht hn
  have harg : originalPeriodPath t 1+(1+I*t) = originalPeriodPath t (-1)+2 := by
    unfold originalPeriodPath
    push_cast
    ring
  rw [harg,thetaZeta_add_two] at hq
  unfold thetaW
  have hdiff : originalPeriodPath t 1-originalPeriodPath t (-1) = 1-I*t := by
    unfold originalPeriodPath
    push_cast
    ring
  linear_combination -hq - thetaEtaExpression t*hdiff

/-- The full complex boundary term for integration by parts on the manuscript's
moving lattice period. It is the term canceled by the moving path derivative. -/
theorem original_weighted_spatial_integral {t : ℝ} (ht : 0 < t) (a : ℝ) :
    slopingIntegral t (fun z => thetaW t z*deriv (thetaA t a) z) =
      slopingIntegral t (fun z => ((rhombicPeriodPair t ht).weierstrassP z+
        thetaEtaExpression t)*thetaA t a z)+
      (Real.pi : ℂ)*I*thetaA t a (originalPeriodPath t (-1)) := by
  let z := originalPeriodPath t
  let A := fun s : ℝ => thetaA t a (z s)
  let P := fun s : ℝ => (rhombicPeriodPair t ht).weierstrassP (z s)
  let W := fun s : ℝ => thetaW t (z s)
  let D := fun s : ℝ => deriv (thetaA t a) (z s)
  let q : ℂ := (1-I*t)/2
  have hn (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) :
      z s ∉ (rhombicPeriodPair t ht).lattice :=
    rhombic_open_rectangle_not_mem ht (originalPeriodPath_mem_rectangle ht hs)
  have hW (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) :
      HasDerivAt W (-(P s+thetaEtaExpression t)*q) s :=
    (thetaW_hasDerivAt ht (hn s hs)).comp s (originalPeriodPath_hasDerivAt t s)
  have hA (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) :
      HasDerivAt A (D s*q) s :=
    (thetaA_differentiableAt ht a (originalPath_regular ht hs)).hasDerivAt.comp s
      (originalPeriodPath_hasDerivAt t s)
  have hWc : ContinuousOn W (Icc (-1 : ℝ) 1) :=
    fun s hs => (hW s hs).continuousAt.continuousWithinAt
  have hAc : ContinuousOn A (Icc (-1 : ℝ) 1) :=
    fun s hs => (hA s hs).continuousAt.continuousWithinAt
  have hPc : ContinuousOn P (Icc (-1 : ℝ) 1) := by
    intro s hs
    exact ((rhombicPeriodPair t ht).analyticOnNhd_weierstrassP _ (hn s hs)).continuousAt.comp_continuousWithinAt
      (f := z) (by dsimp [z]; unfold originalPeriodPath; fun_prop)
  have hDc : ContinuousOn D (Icc (-1 : ℝ) 1) := originalPath_derivative_continuousOn ht a
  have h1 : IntervalIntegrable (fun s : ℝ => W s*D s) volume (-1) 1 :=
    (hWc.mul hDc).intervalIntegrable_of_Icc (by norm_num)
  have h2 : IntervalIntegrable (fun s : ℝ => (P s+thetaEtaExpression t)*A s) volume (-1) 1 :=
    ((hPc.add continuousOn_const).mul hAc).intervalIntegrable_of_Icc (by norm_num)
  have hp (s : ℝ) (hs : s ∈ uIcc (-1 : ℝ) 1) :
      HasDerivAt (fun r : ℝ => W r*A r)
        (q*(W s*D s-(P s+thetaEtaExpression t)*A s)) s := by
    have hs' : s ∈ Icc (-1 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hs
    convert (hW s hs').mul (hA s hs') using 1
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hp ((h1.sub h2).const_mul q)
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub h1 h2] at hi
  have hAe : A 1 = A (-1) := originalPath_kernel_endpoints ht a
  have hWe : W 1 = W (-1)+(Real.pi : ℂ)*I := thetaW_original_endpoints ht
  rw [hAe,hWe] at hi
  change q*(∫ s : ℝ in (-1)..1, W s*D s) =
    q*(∫ s : ℝ in (-1)..1, (P s+thetaEtaExpression t)*A s)+(Real.pi : ℂ)*I*A (-1)
  linear_combination hi

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.original_weighted_spatial_integral
