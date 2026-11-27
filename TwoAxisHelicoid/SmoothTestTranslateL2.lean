import TwoAxisHelicoid.PlaneGradientTranslations
import Mathlib.Analysis.Calculus.ContDiff.RCLike

namespace TwoAxisHelicoid
open MeasureTheory Complex Metric Set Filter Topology
open scoped ContDiff NNReal

/-- A uniform second-order remainder for compactly supported smooth test fields. -/
theorem plane_test_uniform_taylor {f : ℂ → ℂ} (s : ContDiff ℝ ∞ f) (h : HasCompactSupport f) :
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

/-- Difference quotients of translated compact tests converge strongly in L²,
with the usual directional derivative as their limit. -/
theorem compact_test_translate_quotient_tendsto {f : ℂ → ℂ} (s : ContDiff ℝ ∞ f) (h : HasCompactSupport f)
    (w : Lp ℂ 2 (volume:Measure ℂ)) (rep : ⇑w =ᵐ[volume] f) (d : ℂ)
    (v : Lp ℂ 2 (volume:Measure ℂ)) (dv : ⇑v =ᵐ[volume] (fun z => fderiv ℝ f z d)) :
    Tendsto (fun a : ℝ => a⁻¹ • (planeFieldTranslate (a • d) w-w)) (𝓝[>] 0) (𝓝 v) := by
  obtain ⟨L,est⟩ := plane_test_uniform_taylor s h
  obtain ⟨R,_,cover⟩ := h.isBounded.subset_ball_lt 0 (0:ℂ)
  let disk := diskConstantVector 0 (R+‖d‖) 1
  have bound (a : ℝ) (a0 : 0<a) (a1 : a≤1) :
      ‖a⁻¹ • (planeFieldTranslate (a • d) w-w)-v‖≤((L:ℝ)*‖d‖^2*‖disk‖)*a := by
    let t := a • d
    let q := planeFieldTranslate t w-w
    have err : ‖a⁻¹ • q-v‖≤((L:ℝ)*‖d‖^2*a)*‖disk‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      have tr := (measurePreserving_add_right volume t).quasiMeasurePreserving.ae_eq_comp rep
      filter_upwards [Lp.coeFn_sub (a⁻¹ • q) v,Lp.coeFn_smul a⁻¹ q,Lp.coeFn_sub (planeFieldTranslate t w) w,
        planeFieldTranslate_ae t w,rep,tr,dv,diskConstantVector_ae 0 (R+‖d‖) 1]
        with z sub sm dif shift val orig der diskval
      change w (z+t)=f (z+t) at orig
      change ‖(a⁻¹ • q-v) z‖≤_ * ‖disk z‖
      rw [sub,Pi.sub_apply,sm,Pi.smul_apply,dif,Pi.sub_apply,shift,val,orig,der,diskval]
      by_cases inside : z∈ball (0:ℂ) (R+‖d‖)
      · rw [indicator_of_mem inside,norm_one,mul_one]
        have alg : a⁻¹ • (f (z+t)-f z)-fderiv ℝ f z d =
            a⁻¹ • (f (z+t)-f z-fderiv ℝ f z t) := by
          rw [show fderiv ℝ f z t=a • fderiv ℝ f z d from map_smul _ _ _]
          rw [smul_sub a⁻¹ (f (z+t)-f z),inv_smul_smul₀ a0.ne']
        rw [alg,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr a0)]
        have upper := mul_le_mul_of_nonneg_left (est z t) (inv_pos.mpr a0).le
        refine upper.trans_eq ?_
        dsimp only [t]
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos a0]
        field_simp
      · have far : R+‖d‖≤‖z‖ := by simpa [mem_ball,dist_eq_norm] using inside
        have out : z∉tsupport f := by
          intro m
          have small := cover m
          simp [mem_ball,dist_eq_norm] at small
          linarith [norm_nonneg d]
        have outt : z+t∉tsupport f := by
          intro m
          have small := cover m
          simp [mem_ball,dist_eq_norm] at small
          have dt : ‖t‖≤‖d‖ := by
            rw [show t=a • d from rfl,norm_smul,Real.norm_eq_abs,abs_of_pos a0]
            exact mul_le_of_le_one_left (norm_nonneg _) a1
          have tri : ‖z‖≤‖z+t‖+‖t‖ := by simpa using norm_sub_le (z+t) t
          linarith
        simp [image_eq_zero_of_notMem_tsupport outt,image_eq_zero_of_notMem_tsupport out,
          fderiv_of_notMem_tsupport ℝ out,indicator_of_notMem inside]
    calc
      _ ≤ _ := err
      _ = _ := by ring
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have near : ∀ᶠ a : ℝ in 𝓝[>] 0, a∈Ioc (0:ℝ) 1 := Ioc_mem_nhdsGT (by norm_num)
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (near.mono fun a ha => bound a ha.1 ha.2)
  let C := (L:ℝ)*‖d‖^2*‖disk‖
  have lim : Tendsto (fun a : ℝ => C*a) (𝓝[>] 0) (𝓝 (C*0)) :=
    tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds)
  simpa only [mul_zero] using lim
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.plane_test_uniform_taylor
#print axioms TwoAxisHelicoid.compact_test_translate_quotient_tendsto
