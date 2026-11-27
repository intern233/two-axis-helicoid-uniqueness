import TwoAxisHelicoid.SmoothOrbitWeakDerivatives
import TwoAxisHelicoid.SchwartzTranslateDomination
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace TwoAxisHelicoid
open MeasureTheory Complex Set Filter Topology TemperedDistribution
open scoped SchwartzMap ContDiff LineDeriv

/-- The actual derivative of the translation orbit in the energy norm. -/
noncomputable def planeOrbitDirection (u : Lp ℂ 2 (volume : Measure ℂ)) (d : ℂ) :
    Lp ℂ 2 (volume : Measure ℂ) := fderiv ℝ (fun t : ℂ => planeFieldTranslate t u) 0 d

theorem plane_orbit_direction_translate (u : Lp ℂ 2 (volume : Measure ℂ))
    (s : ContDiff ℝ ∞ (fun t : ℂ => planeFieldTranslate t u)) (d t : ℂ) :
    planeFieldTranslate t (planeOrbitDirection u d) =
      fderiv ℝ (fun x : ℂ => planeFieldTranslate x u) t d := by
  let F := fun t : ℂ => planeFieldTranslate t u
  have df : Differentiable ℝ F := s.differentiable (by simp)
  have id : (fun x => F (x+t))=(planeFieldTranslate t).toContinuousLinearMap ∘ F :=
    funext fun x => planeFieldTranslate_add x t u
  have eq := congrArg (fun g : ℂ → Lp ℂ 2 (volume : Measure ℂ) => fderiv ℝ g 0 d) id
  rw [fderiv_comp_add_right,zero_add,fderiv_comp 0 (planeFieldTranslate t).toContinuousLinearMap.differentiableAt (df 0),
    ContinuousLinearMap.fderiv] at eq
  exact eq.symm

/-- Integration against arbitrary Schwartz tests identifies the explicit
strong derivative with the distributional derivative. -/
theorem plane_explicit_orbit_tempered_derivative (u : Lp ℂ 2 (volume : Measure ℂ))
    (s : ContDiff ℝ ∞ (fun t : ℂ => planeFieldTranslate t u)) (d : ℂ) :
    ∂_{d} (u : 𝓢'(ℂ, ℂ)) = (planeOrbitDirection u d : 𝓢'(ℂ, ℂ)) := by
  let F := fun t : ℂ => planeFieldTranslate t u
  let q := fderiv ℝ F 0 d
  have df : Differentiable ℝ F := s.differentiable (by simp)
  have line : HasDerivAt (fun a : ℝ => a • d) d 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const d
  have curve : HasDerivAt (fun a : ℝ => F (a • d)) q 0 :=
    (df 0).hasFDerivAt.comp_hasDerivAt_of_eq 0 line (by simp)
  ext φ
  let D := ∂_{d} φ
  let J : Lp ℂ 2 (volume : Measure ℂ) →L[ℝ] ℂ :=
    ((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp
      (Lp.toTemperedDistributionCLM ℂ volume 2)).restrictScalars ℝ
  have val (v : Lp ℂ 2 (volume : Measure ℂ)) : J v=(∫ z, φ z*v z) :=
    Lp.toTemperedDistribution_apply v φ
  let G := fun (a : ℝ) (z : ℂ) => φ (z-a • d)*u z
  let H := fun (a : ℝ) (z : ℂ) => -D (z-a • d)*u z
  have swap (a : ℝ) : J (F (a • d)) = ∫ z, G a z := by
    rw [val]
    calc
      _ = (∫ z : ℂ, G a (z+a • d)) := by
        apply integral_congr_ae
        filter_upwards [planeFieldTranslate_ae (a • d) u] with z hz
        simp only [F,hz,G,add_sub_cancel_right]
      _ = _ := integral_add_right_eq_self _ _
  obtain ⟨w,wm,dom⟩ := plane_schwartz_shift_domination D (norm_nonneg d)
  have measurable (a : ℝ) : AEStronglyMeasurable (G a) volume :=
    ((φ.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable).mul (Lp.aestronglyMeasurable u)
  have atzero : Integrable (G 0) := by
    have p := (φ.memLp 2 volume).integrable_mul (Lp.memLp u)
    change Integrable (fun z : ℂ => φ z*u z) volume at p
    simpa only [G,zero_smul,sub_zero] using! p
  have m0 : AEStronglyMeasurable (H 0) volume := by
    have p := D.continuous.neg.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u)
    change AEStronglyMeasurable (fun z : ℂ => -D z*u z) volume at p
    simpa only [H,zero_smul,sub_zero] using! p
  have bd (z : ℂ) (a : ℝ) (ha : a∈Metric.ball 0 1) : ‖H a z‖≤w z*‖u z‖ := by
    have ha' : ‖a‖≤1 := (show ‖a‖<1 by simpa [Metric.mem_ball] using ha).le
    have ht : ‖-(a • d)‖≤‖d‖ := by
      rw [norm_neg,norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) ha'
    simpa only [H,norm_mul,norm_neg,sub_eq_add_neg] using
      mul_le_mul_of_nonneg_right (dom z (-(a • d)) ht) (norm_nonneg (u z))
  have deriv (z : ℂ) (a : ℝ) : HasDerivAt (fun t => G t z) (H a z) a := by
    have l : HasDerivAt (fun t : ℝ => z-t • d) (-d) a := by
      simpa only [zero_sub,one_smul,id_eq] using! (hasDerivAt_const a z).sub ((hasDerivAt_id a).smul_const d)
    have k := ((φ.differentiable (z-a • d)).hasFDerivAt.comp_hasDerivAt a l).mul_const (u z)
    simpa only [G,H,D,SchwartzMap.lineDerivOp_apply_eq_fderiv,map_neg,Function.comp_apply] using k
  have actual := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds (0:ℝ) zero_lt_one)
    (Eventually.of_forall measurable) atzero m0 (ae_of_all _ bd) (wm.integrable_mul (Lp.memLp u).norm)
    (ae_of_all _ (fun z a _ => deriv z a))).2
  have paired : HasDerivAt (fun a : ℝ => J (F (a • d))) (J q) 0 := J.hasFDerivAt.comp_hasDerivAt 0 curve
  rw [show (fun a : ℝ => J (F (a • d)))=(fun a => ∫ z, G a z) from funext swap] at paired
  have eq := paired.unique actual
  rw [val] at eq
  rw [TemperedDistribution.lineDerivOp_apply_apply]
  change (Lp.toTemperedDistribution u) (-D)=(Lp.toTemperedDistribution q) φ
  rw [Lp.toTemperedDistribution_apply,Lp.toTemperedDistribution_apply]
  simpa only [H,zero_smul,sub_zero,neg_apply,smul_eq_mul] using eq.symm

theorem plane_smooth_orbit_tempered_derivative (u : Lp ℂ 2 (volume : Measure ℂ))
    (s : ContDiff ℝ ∞ (fun t : ℂ => planeFieldTranslate t u)) (d : ℂ) :
    ∃ q : Lp ℂ 2 (volume : Measure ℂ),
      ∂_{d} (u : 𝓢'(ℂ, ℂ)) = (q : 𝓢'(ℂ, ℂ)) ∧
      ContDiff ℝ ∞ (fun t : ℂ => planeFieldTranslate t q) := by
  refine ⟨planeOrbitDirection u d,plane_explicit_orbit_tempered_derivative u s d,?_⟩
  simp_rw [plane_orbit_direction_translate u s d]
  exact (s.fderiv_right (by simp)).clm_apply contDiff_const

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.plane_explicit_orbit_tempered_derivative
#print axioms TwoAxisHelicoid.plane_smooth_orbit_tempered_derivative
