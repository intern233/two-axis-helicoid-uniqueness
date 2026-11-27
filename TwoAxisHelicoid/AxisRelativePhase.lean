import TwoAxisHelicoid.AxisEndRegularity

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped Interval Topology
attribute [local irreducible] thetaGauss thetaZeta thetaEtaExpression

theorem rhombic_vertical_strip_not_mem {t x y : ℝ} (ht : 0 < t)
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) (2*t)) :
    (x : ℂ)+I*y ∉ (rhombicPeriodPair t ht).lattice := by
  intro hz
  obtain ⟨m,n,hr,hi⟩ := (rhombic_mem_lattice_iff ht _).mp hz
  norm_num [Complex.mul_re,Complex.mul_im] at hr hi
  have hn0 : (0 : ℤ) < n := by
    exact_mod_cast (show (0 : ℝ) < n by nlinarith [hy.1])
  have hn2 : n < (2 : ℤ) := by
    exact_mod_cast (show (n : ℝ) < 2 by nlinarith [hy.2])
  have hn : n = 1 := by omega
  subst n
  norm_num at hr
  have hm0 : m < (0 : ℤ) := by
    exact_mod_cast (show (m : ℝ) < 0 by linarith [hx.2])
  have hm1 : (-1 : ℤ) < m := by
    exact_mod_cast (show (-1 : ℝ) < m by linarith [hx.1])
  omega

theorem axisRegularCoefficient_den_re_neg {t a y : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) (2*t)) :
    ((rhombicPeriodPair t ht).weierstrassP (I*y)-
      (rhombicPeriodPair t ht).weierstrassP a).re < 0 := by
  have he := rhombic_weierstrassP_imaginary_le_one ht hy
  have hu := rhombic_weierstrassP_strictAnti_to_one ht
    ⟨ha.1,ha.2.le⟩ (by norm_num : (1 : ℝ) ∈ Ioc 0 1) ha.2
  simp only [Complex.ofReal_one] at hu
  simp only [Complex.sub_re]
  linarith

theorem axisRegularCoefficient_continuousAt_imaginary {t a y : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) (2*t)) :
    ContinuousAt (fun s : ℝ => (axisRegularCoefficient t ht a (I*s)).re) y := by
  have hz : I*(y : ℂ) ∉ (rhombicPeriodPair t ht).lattice := by
    simpa only [Complex.ofReal_zero,zero_add] using
      rhombic_vertical_strip_not_mem ht (by norm_num : (0 : ℝ) ∈ Ioo (-1) 1) hy
  have hden : (rhombicPeriodPair t ht).weierstrassP (I*y)-
      (rhombicPeriodPair t ht).weierstrassP a ≠ 0 := by
    intro he
    have hn := axisRegularCoefficient_den_re_neg ht ha hy
    rw [he,Complex.zero_re] at hn
    exact lt_irrefl _ hn
  have hP := (rhombicPeriodPair t ht).analyticOnNhd_weierstrassP (I*y) hz
  have hq : AnalyticAt ℂ (axisRegularCoefficient t ht a) (I*y) :=
    analyticAt_const.add (analyticAt_const.div (hP.sub analyticAt_const) hden)
  exact Complex.continuous_re.continuousAt.comp
    (hq.continuousAt.comp (f := fun s : ℝ => I*(s : ℂ)) (by fun_prop))

noncomputable def axisRelativePhase (t : ℝ) (ht : 0 < t) (a y : ℝ) : ℝ :=
  ∫ s : ℝ in t..y, (axisRegularCoefficient t ht a (I*s)).re

theorem axisRelativePhase_hasDerivAt {t a y : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) (2*t)) :
    HasDerivAt (axisRelativePhase t ht a) (axisRegularCoefficient t ht a (I*y)).re y := by
  have hc : ContinuousOn (fun s : ℝ => (axisRegularCoefficient t ht a (I*s)).re)
      (Ioo 0 (2*t)) :=
    fun s hs => (axisRegularCoefficient_continuousAt_imaginary ht ha hs).continuousWithinAt
  have hsub : uIcc t y ⊆ Ioo (0 : ℝ) (2*t) := by
    intro s hs
    rcases le_total t y with h | h
    · rw [uIcc_of_le h] at hs
      exact ⟨ht.trans_le hs.1,hs.2.trans_lt hy.2⟩
    · rw [uIcc_of_ge h] at hs
      exact ⟨hy.1.trans_le hs.1,hs.2.trans_lt (by linarith : t < 2*t)⟩
  have hI : IntervalIntegrable (fun s : ℝ => (axisRegularCoefficient t ht a (I*s)).re)
      volume t y := (hc.mono hsub).intervalIntegrable
  exact intervalIntegral.integral_hasDerivAt_right hI
    (hc.stronglyMeasurableAtFilter isOpen_Ioo y hy)
    (axisRegularCoefficient_continuousAt_imaginary ht ha hy)

theorem axisRelativePhase_strictMonoOn {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    StrictMonoOn (axisRelativePhase t ht a) (Ioo 0 (2*t)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 (2*t))
  · intro y hy
    exact (axisRelativePhase_hasDerivAt ht ha hy).continuousAt.continuousWithinAt
  · intro y hy
    have hy' := interior_subset hy
    rw [(axisRelativePhase_hasDerivAt ht ha hy').deriv]
    exact axisRegularCoefficient_imaginary_pos ht ha hy'

theorem axisRelativePhase_actual_differential {t a c y : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hy : y ∈ Ioo (0 : ℝ) (2*t)) :
    HasDerivAt (axisRelativePhase t ht a)
      (deriv (thetaGauss t a 1) (I*y)/thetaGauss t a 1 (I*y)-
        I*((2*(a-1)/c : ℝ) : ℂ)*(coordinateData t a c ht (I*y) 2)).re y := by
  have hz : I*(y : ℂ) ∉ (rhombicPeriodPair t ht).lattice := by
    simpa only [Complex.ofReal_zero,zero_add] using
      rhombic_vertical_strip_not_mem ht (by norm_num : (0 : ℝ) ∈ Ioo (-1) 1) hy
  have hm : I*(y : ℂ)-a ∉ (rhombicPeriodPair t ht).lattice := by
    have h := rhombic_vertical_strip_not_mem ht
      (show -a ∈ Ioo (-1 : ℝ) 1 by constructor <;> linarith [ha.1,ha.2]) hy
    simpa only [Complex.ofReal_neg,sub_eq_add_neg,add_comm] using h
  have hp : I*(y : ℂ)+a ∉ (rhombicPeriodPair t ht).lattice := by
    simpa only [add_comm] using rhombic_vertical_strip_not_mem ht
      (show a ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith [ha.1],ha.2⟩) hy
  rw [actualGauss_end_regular_coefficient ht ha hc hz hm hp]
  exact axisRelativePhase_hasDerivAt ht ha hy

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.axisRelativePhase_strictMonoOn
#print axioms TwoAxisHelicoid.axisRelativePhase_actual_differential
