import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Complex Metric Set Filter Topology
open scoped ContDiff NNReal BoundedContinuousFunction

/-- Translated compact coefficients as actual bounded functions, with the
uniform norm appropriate to their action on L² fields. -/
noncomputable def compactCoefficientTranslate (f : ℂ → ℝ) (s : Continuous f) (h : HasCompactSupport f)
    (t : ℂ) : ℂ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun z => f (z+t)) (s.comp (continuous_id.add continuous_const))
    (h.exists_bound_of_continuous s).choose (fun z => (h.exists_bound_of_continuous s).choose_spec (z+t))

private theorem coefficient_taylor {f : ℂ → ℝ} (s : ContDiff ℝ ∞ f) (h : HasCompactSupport f) :
    ∃ L : ℝ≥0, ∀ z t : ℂ, ‖f (z+t)-f z-fderiv ℝ f z t‖≤(L:ℝ)*‖t‖^2 := by
  have sd : ContDiff ℝ ∞ (fderiv ℝ f) := s.fderiv_right (by simp)
  obtain ⟨L,lip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (h.fderiv ℝ) sd (by simp)
  refine ⟨L,fun z t => ?_⟩
  have bd (y : ℂ) (hy : y∈closedBall z ‖t‖) : ‖fderiv ℝ f y-fderiv ℝ f z‖ ≤ (L:ℝ)*‖t‖ := by
    exact (lip.norm_sub_le y z).trans (mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using mem_closedBall.mp hy) L.coe_nonneg)
  have est := (convex_closedBall z ‖t‖).norm_image_sub_le_of_norm_fderiv_le'
    (fun y _ => s.differentiable (by simp) y) bd (mem_closedBall_self (norm_nonneg t))
    (show z+t∈closedBall z ‖t‖ by simp [mem_closedBall,dist_eq_norm])
  simpa [pow_two,mul_assoc] using est

private theorem coefficient_direction_smooth {f : ℂ → ℝ} (s : ContDiff ℝ ∞ f) (d : ℂ) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ f z d) :=
  (s.fderiv_right (by simp)).clm_apply contDiff_const

private noncomputable def coefficientDifferential {f : ℂ → ℝ}
    (s : ContDiff ℝ ∞ f) (h : HasCompactSupport f) (t : ℂ) : ℂ →L[ℝ] (ℂ →ᵇ ℝ) :=
  Complex.reCLM.smulRight (compactCoefficientTranslate _ (coefficient_direction_smooth s 1).continuous (h.fderiv_apply ℝ 1) t) +
    Complex.imCLM.smulRight (compactCoefficientTranslate _ (coefficient_direction_smooth s I).continuous (h.fderiv_apply ℝ I) t)

private theorem coefficientDifferential_apply {f : ℂ → ℝ} (s : ContDiff ℝ ∞ f) (h : HasCompactSupport f)
    (t d z : ℂ) : coefficientDifferential s h t d z = fderiv ℝ f (z+t) d := by
  change d.re*fderiv ℝ f (z+t) 1+d.im*fderiv ℝ f (z+t) I=fderiv ℝ f (z+t) d
  conv_rhs => rw [show d=d.re • (1:ℂ)+d.im • I by simp]
  simp only [map_add,map_smul,smul_eq_mul]

private theorem hasFDerivAt_compactCoefficientTranslate {f : ℂ → ℝ} (s : ContDiff ℝ ∞ f)
    (h : HasCompactSupport f) (t : ℂ) :
    HasFDerivAt (compactCoefficientTranslate f s.continuous h) (coefficientDifferential s h t) t := by
  obtain ⟨L,est⟩ := coefficient_taylor s h
  rw [hasFDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro c hc
  have lp : 0<(L:ℝ)+1 := by positivity
  filter_upwards [Metric.ball_mem_nhds t (div_pos hc lp)] with y hy
  have sm : ‖y-t‖<(c/((L:ℝ)+1)) := by simpa only [mem_ball,dist_eq_norm] using hy
  have prod : (L:ℝ)*‖y-t‖≤c := by
    have x := (lt_div_iff₀ lp).mp sm
    nlinarith [norm_nonneg (y-t)]
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hc.le (norm_nonneg _))).mpr
  intro z
  change ‖f (z+y)-f (z+t)-coefficientDifferential s h t (y-t) z‖≤_
  rw [coefficientDifferential_apply]
  have e := est (z+t) (y-t)
  rw [show z+t+(y-t)=z+y by abel] at e
  exact e.trans (by simpa only [pow_two,mul_assoc] using mul_le_mul_of_nonneg_right prod (norm_nonneg (y-t)))

/-- All derivatives of the coefficient-translation map exist in the uniform
norm. The proof uses a uniform Taylor remainder and differentiates the two
actual coordinate derivatives repeatedly. -/
theorem smooth_compactCoefficientTranslate {f : ℂ → ℝ} (s : ContDiff ℝ ∞ f) (h : HasCompactSupport f) :
    ContDiff ℝ ∞ (compactCoefficientTranslate f s.continuous h) := by
  apply contDiff_iff_forall_nat_le.mpr
  intro n unused
  clear unused
  induction n generalizing f with
  | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun z => (hasFDerivAt_compactCoefficientTranslate s h z).continuousAt)
  | succ n ih =>
    rw [Nat.cast_succ]
    apply contDiff_succ_iff_fderiv.mpr
    have df : fderiv ℝ (compactCoefficientTranslate f s.continuous h)=coefficientDifferential s h :=
      funext fun z => (hasFDerivAt_compactCoefficientTranslate s h z).fderiv
    refine ⟨fun z => (hasFDerivAt_compactCoefficientTranslate s h z).differentiableAt,?_,?_⟩
    · simp
    · rw [df]
      exact (contDiff_const.smulRight (ih (coefficient_direction_smooth s 1) (h.fderiv_apply ℝ 1))).add
        (contDiff_const.smulRight (ih (coefficient_direction_smooth s I) (h.fderiv_apply ℝ I)))
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_compactCoefficientTranslate
