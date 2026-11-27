import TwoAxisHelicoid.PlaneWeakIntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

namespace TwoAxisHelicoid
open MeasureTheory Complex Set Filter InnerProductSpace
open scoped ContDiff RealInnerProductSpace

theorem plane_smooth_test_integration_by_parts {a φ : ℂ → ℝ} (sa : ContDiff ℝ ∞ a)
    (s : ContDiff ℝ ∞ φ) (h : HasCompactSupport φ) (d : ℂ) :
    (∫ z, a z*fderiv ℝ φ z d) = -(∫ z, fderiv ℝ a z d * φ z) := by
  have ac : Continuous (fun z => fderiv ℝ a z d) := (sa.continuous_fderiv (by simp)).clm_apply continuous_const
  have fc : Continuous (fun z => fderiv ℝ φ z d) := (s.continuous_fderiv (by simp)).clm_apply continuous_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((ac.mul s.continuous).integrable_of_hasCompactSupport h.mul_left)
    ((sa.continuous.mul fc).integrable_of_hasCompactSupport (h.fderiv_apply ℝ d).mul_left)
    ((sa.continuous.mul s.continuous).integrable_of_hasCompactSupport h.mul_left)
    (fun z _ => sa.differentiable (by simp) z) (fun z _ => s.differentiable (by simp) z)

theorem smooth_plane_flux_divergence_zero {U : Set ℂ} (op : IsOpen U) {a b : ℂ → ℝ}
    (sa : ContDiff ℝ ∞ a) (sb : ContDiff ℝ ∞ b)
    (weak : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z, a z*fderiv ℝ φ z 1+b z*fderiv ℝ φ z I)=0) :
    ∀ z∈U, fderiv ℝ a z 1+fderiv ℝ b z I=0 := by
  let div := fun z => fderiv ℝ a z 1+fderiv ℝ b z I
  have ac : Continuous (fun z => fderiv ℝ a z 1) := (sa.continuous_fderiv (by simp)).clm_apply continuous_const
  have bc : Continuous (fun z => fderiv ℝ b z I) := (sb.continuous_fderiv (by simp)).clm_apply continuous_const
  have dc : Continuous div := ac.add bc
  have ae : ∀ᵐ z : ℂ, z∈U → div z=0 := by
    apply op.ae_eq_zero_of_integral_contDiff_smul_eq_zero (dc.continuousOn.locallyIntegrableOn op.measurableSet)
    intro φ s h inside
    have c (d : ℂ) : Continuous (fun z => fderiv ℝ φ z d) :=
      (s.continuous_fderiv (by simp)).clm_apply continuous_const
    have sum := weak φ s h inside
    rw [integral_add (f:=fun z => a z*fderiv ℝ φ z 1) (g:=fun z => b z*fderiv ℝ φ z I) ((sa.continuous.mul (c 1)).integrable_of_hasCompactSupport (h.fderiv_apply ℝ 1).mul_left)
      ((sb.continuous.mul (c I)).integrable_of_hasCompactSupport (h.fderiv_apply ℝ I).mul_left),
      plane_smooth_test_integration_by_parts sa s h,plane_smooth_test_integration_by_parts sb s h] at sum
    have id (z : ℂ) : φ z • div z=fderiv ℝ a z 1*φ z+fderiv ℝ b z I*φ z := by
      dsimp [div]
      ring
    simp_rw [id]
    rw [integral_add (f:=fun z => fderiv ℝ a z 1*φ z) (g:=fun z => fderiv ℝ b z I*φ z) ((ac.mul s.continuous).integrable_of_hasCompactSupport h.mul_left)
      ((bc.mul s.continuous).integrable_of_hasCompactSupport h.mul_left)]
    linarith
  exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' op.measurableSet).mpr ae) op dc.continuousOn continuousOn_const

/-- A smooth representative of an actual weak gradient on an open piece
satisfies the manuscript's pointwise scalar equation everywhere there. -/
theorem smooth_gradient_of_weak_flux_is_harmonic {U : Set ℂ} (op : IsOpen U)
    {A B C f : ℂ → ℝ} (sa : ContDiff ℝ ∞ A) (sb : ContDiff ℝ ∞ B) (sc : ContDiff ℝ ∞ C)
    (sf : ContDiff ℝ ∞ f) {u : Lp ℂ 2 (volume:Measure ℂ)}
    (repr : ∀ᵐ z : ℂ, z∈U → 1+u z=planeTestGradient f z)
    (weak : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z, ⟪planeMetricFlux A B C z (1+u z),planeTestGradient φ z⟫_ℝ) = 0) :
    ∀ z∈U, fderiv ℝ (fun y => C y*fderiv ℝ f y 1-B y*fderiv ℝ f y I) z 1 =
      fderiv ℝ (fun y => B y*fderiv ℝ f y 1-A y*fderiv ℝ f y I) z I := by
  let a := fun z => C z*fderiv ℝ f z 1-B z*fderiv ℝ f z I
  let b := fun z => A z*fderiv ℝ f z I-B z*fderiv ℝ f z 1
  have sm (d : ℂ) : ContDiff ℝ ∞ (fun z => fderiv ℝ f z d) :=
    (sf.fderiv_right (by simp)).clm_apply contDiff_const
  have div := smooth_plane_flux_divergence_zero (a:=a) (b:=b) op
    ((sc.mul (sm 1)).sub (sb.mul (sm I))) ((sa.mul (sm I)).sub (sb.mul (sm 1)))
  have eq : ∀ z∈U, fderiv ℝ a z 1+fderiv ℝ b z I=0 := by
    apply div
    intro φ s h inside
    refine (integral_congr_ae ?_).trans (weak φ s h inside)
    filter_upwards [repr] with z hz
    by_cases mem : z∈U
    · rw [hz mem]
      simp only [Complex.inner,planeTestGradient,planeMetricFlux,Complex.mul_re,Complex.conj_re,Complex.conj_im,a,b]
      ring
    · have out : z∉tsupport φ := fun m => mem (inside m)
      rw [real_inner_comm,planeTestGradient_pair]
      simp [fderiv_of_notMem_tsupport ℝ out]
  have neg : (fun y => B y*fderiv ℝ f y 1-A y*fderiv ℝ f y I)=fun y => -b y := by
    funext z
    dsimp [b]
    ring
  intro z hz
  rw [neg,fderiv_fun_neg]
  change fderiv ℝ a z 1= -fderiv ℝ b z I
  linarith [eq z hz]
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_plane_flux_divergence_zero
#print axioms TwoAxisHelicoid.smooth_gradient_of_weak_flux_is_harmonic
