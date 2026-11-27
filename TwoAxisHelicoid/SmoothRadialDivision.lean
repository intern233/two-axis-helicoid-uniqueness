import TwoAxisHelicoid.CompactParameterCOneIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Set Filter Metric MeasureTheory
open scoped Topology Interval ContDiff
universe u

private theorem parameter_integral_has_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E × ℝ → G} (sm : ContDiff ℝ 1 F) (a b : ℝ) (x : E) :
    HasFDerivAt (fun y : E => ∫ t in a..b, F (y,t))
      (∫ t in a..b, (fderiv ℝ F (x,t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
  let D := fun p : E × ℝ => (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have cd : Continuous D := (sm.continuous_fderiv one_ne_zero).clm_comp continuous_const
  have sec (y : E) : Continuous (fun t : ℝ => F (y,t)) := sm.continuous.comp (continuous_const.prodMk continuous_id)
  have secD (y : E) : Continuous (fun t : ℝ => D (y,t)) := cd.comp (continuous_const.prodMk continuous_id)
  obtain ⟨M,bound⟩ := ((isCompact_closedBall x 1).prod isCompact_uIcc).exists_bound_of_continuousOn cd.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le'' (F:=fun y t => F (y,t))
    (F':=fun y t => D (y,t)) (bound:=fun _ => M) (ball_mem_nhds x zero_lt_one)
  · exact .of_forall (fun y => (sec y).aestronglyMeasurable)
  · exact (sec x).intervalIntegrable a b
  · exact (secD x).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_uIoc (a:=a) (b:=b))] with t ht
    intro y hy
    exact bound (y,t) ⟨ball_subset_closedBall hy,uIoc_subset_uIcc ht⟩
  · exact intervalIntegrable_const
  · exact .of_forall (fun t y _ => ((sm.differentiable one_ne_zero (y,t)).hasFDerivAt).comp y
      (hasFDerivAt_prodMk_left y t))

/-- Joint smoothness is preserved when integrating over a fixed compact
interval. Differentiation produces the actual integral of the partial
Fréchet derivative in the parameter. -/
theorem smooth_compact_parameter_integral
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E × ℝ → G} (sF : ContDiff ℝ ∞ F) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x : E => ∫ t in a..b, F (x,t)) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing G with
  | zero =>
    exact (contDiff_one_compact_parameter_integral (sF.of_le (by norm_num)) a b).of_le (by norm_num)
  | succ n ih =>
    rw [Nat.cast_succ,contDiff_succ_iff_fderiv]
    have d := parameter_integral_has_derivative (sF.of_le (by norm_num)) a b
    refine ⟨fun x => (d x).differentiableAt,by simp,?_⟩
    have ext := funext fun x => (d x).fderiv
    rw [ext]
    exact ih (((contDiff_infty_iff_fderiv.mp sF).2).clm_comp contDiff_const)

/-- Divide a jointly smooth function by the first coordinate after
subtracting its value on that coordinate hyperplane. -/
noncomputable def radialDifferenceQuotient (F : ℝ × ℂ → ℝ) (p : ℝ × ℂ) : ℝ :=
  ∫ t in (0:ℝ)..1, (fderiv ℝ F (t*p.1,p.2)) (1,0)

theorem smooth_radial_difference_quotient {F : ℝ × ℂ → ℝ} (sm : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (radialDifferenceQuotient F) ∧
      ∀ r v, F (r,v)=F (0,v)+r*radialDifferenceQuotient F (r,v) := by
  let P := fun q : (ℝ × ℂ) × ℝ => (q.2*q.1.1,q.1.2)
  have sP : ContDiff ℝ ∞ P := (contDiff_snd.mul (contDiff_fst.comp contDiff_fst)).prodMk (contDiff_snd.comp contDiff_fst)
  have ds := (contDiff_infty_iff_fderiv.mp sm).2
  refine ⟨smooth_compact_parameter_integral ((ds.comp sP).clm_apply (contDiff_const (c:=(1,0)))) 0 1,?_⟩
  intro r v
  let D := fun t : ℝ => (fderiv ℝ F (t*r,v)) (1,0)
  have cd : Continuous D := (ds.continuous.comp ((continuous_id.mul continuous_const).prodMk continuous_const)).clm_apply continuous_const
  have d (t : ℝ) : HasDerivAt (fun s : ℝ => F (s*r,v)) (r*D t) t := by
    have line : HasDerivAt (fun s : ℝ => (s*r,v)) (r,0) t := by
      simpa using ((hasDerivAt_id t).mul_const r).prodMk (hasDerivAt_const t v)
    have eq : ((r,0) : ℝ × ℂ)=r • (1,0) := by simp
    have h := ((sm.differentiable (by norm_num) (t*r,v)).hasFDerivAt).comp_hasDerivAt t line
    simpa only [eq,map_smul,smul_eq_mul,Function.comp_def,D] using h
  have val := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => d t)
    ((continuous_const.mul cd).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at val
  simp only [one_mul,zero_mul] at val
  change F (r,v)=F (0,v)+r*(∫ t in (0:ℝ)..1, D t)
  linarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_radial_difference_quotient
