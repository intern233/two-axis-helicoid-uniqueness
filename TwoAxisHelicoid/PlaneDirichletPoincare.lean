import TwoAxisHelicoid.PlaneWeakConductivity
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace TwoAxisHelicoid
open MeasureTheory Complex Set Metric InnerProductSpace
open scoped ContDiff ENNReal NNReal RealInnerProductSpace

/-- The physical two-component gradient represents the full real Fréchet
derivative with its exact operator norm. -/
theorem planeTestGradient_opNorm (φ : ℂ → ℝ) (z : ℂ) :
    ‖fderiv ℝ φ z‖=‖planeTestGradient φ z‖ := by
  have rep : fderiv ℝ φ z=innerSL ℝ (planeTestGradient φ z) := by
    ext v
    change fderiv ℝ φ z v=⟪planeTestGradient φ z,v⟫_ℝ
    conv_lhs => rw [show v=v.re • (1:ℂ)+v.im • I by simp]
    simp only [map_add,map_smul,smul_eq_mul,Complex.inner,Complex.mul_re,Complex.conj_im,Complex.conj_re,
      planeTestGradient]
    ring
  rw [rep,innerSL_apply_norm]

/-- On a bounded disk the L² gradient determines the scalar test function
continuously, with a single Poincaré constant for all such functions. -/
theorem disk_test_poincare (p : ℂ) (r : ℝ) :
    ∃ D : ℝ, 0≤D ∧ ∀ (φ : ℂ → ℝ) (s : ContDiff ℝ ∞ φ) (h : HasCompactSupport φ),
      tsupport φ ⊆ ball p r →
      ‖(s.continuous.memLp_of_hasCompactSupport (p:=2) (μ:=volume) h).toLp φ‖ ≤
        D*‖(planeTestGradient_memLp (μ:=volume) s h).toLp (planeTestGradient φ)‖ := by
  let U := ball p r
  let μ : Measure ℂ := volume
  let S : ℝ≥0 := eLpNormLESNormFDerivOneConst μ 2
  let M : ℝ≥0∞ := (μ U) ^ (1/2:ℝ)
  have finiteM : M≠⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_ball_lt_top.ne
  refine ⟨(S:ℝ)*M.toReal,by positivity,?_⟩
  intro φ s h inside
  have sm := (s.continuous_fderiv (by simp)).aestronglyMeasurable (μ:=μ)
  have support : Function.support (fderiv ℝ φ) ⊆ U := (support_fderiv_subset ℝ).trans inside
  have cmp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p:=1) (q:=2) (by norm_num) (sm.restrict (s:=U))
  rw [eLpNorm_restrict_eq_of_support_subset sm support,eLpNorm_restrict_eq_of_support_subset sm support,
    Measure.restrict_apply_univ] at cmp
  have cmp' : eLpNorm (fderiv ℝ φ) 1 μ ≤ eLpNorm (fderiv ℝ φ) 2 μ * M := by
    convert cmp using 1
    norm_num [M]
  have hc : NNReal.HolderConjugate (Module.finrank ℝ ℂ) (2:ℝ≥0) := by
    simpa only [Complex.finrank_real_complex,Nat.cast_ofNat] using NNReal.HolderConjugate.two_two
  have sob : eLpNorm φ 2 μ ≤ (S:ℝ≥0∞)*eLpNorm (fderiv ℝ φ) 1 μ := by
    simpa [S] using eLpNorm_le_eLpNorm_fderiv_one μ (s.of_le (by simp)) h hc
  have eq : eLpNorm (fderiv ℝ φ) 2 μ=eLpNorm (planeTestGradient φ) 2 μ :=
    eLpNorm_congr_norm_ae sm (planeTestGradient_memLp s h).aestronglyMeasurable
      (ae_of_all _ (planeTestGradient_opNorm φ))
  have bound : eLpNorm φ 2 μ ≤ (S:ℝ≥0∞)*(eLpNorm (fderiv ℝ φ) 2 μ*M) :=
    sob.trans (by gcongr)
  rw [eq] at bound
  have finiteG := (planeTestGradient_memLp (μ:=μ) s h).eLpNorm_ne_top
  have realBound := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top finiteG finiteM)) bound
  simp only [ENNReal.toReal_mul,ENNReal.coe_toReal] at realBound
  rw [Lp.norm_toLp,Lp.norm_toLp]
  change (eLpNorm φ 2 μ).toReal ≤ _
  convert realBound using 1
  ring
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.disk_test_poincare
