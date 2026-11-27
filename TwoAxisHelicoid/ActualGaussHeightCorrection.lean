import TwoAxisHelicoid.ActualComplexHeight
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaSigma thetaZeta thetaEtaExpression

noncomputable def heightGaussFactor (t a : ℝ) (m : ℤ) (ht : 0 < t) (z : ℂ) : ℂ :=
  -exp ((2*(m : ℂ)*thetaEtaExpression t-
    2*((a : ℂ)-m)*(rhombicPeriodPair t ht).weierstrassP a)*z)*
      thetaSigma t (z-a)/thetaSigma t (z+a)

theorem heightGaussFactor_zero {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) :
    heightGaussFactor t a m ht 0 = 1 := by
  have hn : thetaSigma t a ≠ 0 :=
    (thetaSigma_zero_iff_lattice_of_pos ht ht a).not.mpr
      (real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2]))
  simp [heightGaussFactor,thetaSigma_neg,hn]

theorem heightGaussFactor_analyticAt_zero {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) :
    AnalyticAt ℂ (heightGaussFactor t a m ht) 0 := by
  have hn : thetaSigma t (0+a) ≠ 0 := by
    simpa using (thetaSigma_zero_iff_lattice_of_pos ht ht a).not.mpr
      (real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2]))
  unfold heightGaussFactor
  exact (((analyticAt_const.mul analyticAt_id).cexp.neg).mul
    ((thetaSigma_analyticAt ht _).comp (analyticAt_id.sub analyticAt_const))).div
      ((thetaSigma_analyticAt ht _).comp (analyticAt_id.add analyticAt_const)) hn

theorem gauss_height_factor_identity {t a c : ℝ} (ht : 0 < t) (hc : c ≠ 0)
    (m : ℤ) (z : ℂ) :
    I*thetaGauss t a m z =
      exp (I*((2*(a-m)/c : ℝ) : ℂ)*actualComplexHeight t a c ht z)*
        heightGaussFactor t a m ht z := by
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hexp : I*((2*(a-m)/c : ℝ) : ℂ)*actualComplexHeight t a c ht z+
      (2*(m : ℂ)*thetaEtaExpression t-2*((a : ℂ)-m)*(rhombicPeriodPair t ht).weierstrassP a)*z =
      2*((a : ℂ)-m)*thetaZeta t z+2*(m : ℂ)*thetaEtaExpression t*z := by
    unfold actualComplexHeight
    push_cast
    field_simp [hcC]
    ring_nf
    simp only [I_sq]
    ring
  unfold thetaGauss heightGaussFactor
  rw [← hexp,exp_add]
  ring_nf
  simp only [I_sq]
  ring

/-- In the actual height coordinate, the Gauss map has a holomorphic
correction which vanishes at the puncture, after a fixed quarter turn. -/
theorem actual_gauss_height_holomorphic_correction {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (m : ℤ) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f 0 ∧ f 0 = 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), I*thetaGauss t a m z =
        exp (I*((2*(a-m)/c : ℝ) : ℂ)*actualComplexHeight t a c ht z+f z) := by
  let S := heightGaussFactor t a m ht
  have haS := heightGaussFactor_analyticAt_zero ht ha m
  have hS0 : S 0 = 1 := heightGaussFactor_zero ht ha m
  let f : ℂ → ℂ := fun z => log (S z)
  have hf : AnalyticAt ℂ f 0 :=
    (analyticAt_clog (by rw [hS0]; simp)).comp haS
  refine ⟨f,hf,by simp [f,hS0],?_⟩
  have hn : ∀ᶠ z in 𝓝 (0 : ℂ), S z ≠ 0 :=
    haS.continuousAt.eventually_ne (by change S 0 ≠ 0; rw [hS0]; exact one_ne_zero)
  filter_upwards [hn] with z hz
  rw [gauss_height_factor_identity ht hc m z,exp_add]
  exact congrArg (fun w => exp (I*((2*(a-m)/c : ℝ) : ℂ)*actualComplexHeight t a c ht z)*w)
    (exp_log hz).symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_gauss_height_holomorphic_correction
