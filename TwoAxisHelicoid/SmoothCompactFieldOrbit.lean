import TwoAxisHelicoid.BoundedCoefficientMultiplier
import TwoAxisHelicoid.PlaneGradientTranslations

namespace TwoAxisHelicoid
open MeasureTheory Complex Set Metric Filter Topology
open scoped ContDiff BoundedContinuousFunction

/-- The complete translation orbit of a smooth compactly supported physical
vector field is smooth in the global L² norm. The local cutoff is justified
on one disk for all translations in a neighborhood of each parameter. -/
theorem smooth_compact_field_translation {f : ℂ → ℂ} (s : ContDiff ℝ ∞ f)
    (h : HasCompactSupport f) (b : Lp ℂ 2 (volume:Measure ℂ)) (rep : ⇑b =ᵐ[volume] f) :
    ContDiff ℝ ∞ (fun t : ℂ => planeFieldTranslate t b) := by
  let fr := fun z => (f z).re
  let fi := fun z => (f z).im
  have sr : ContDiff ℝ ∞ fr := Complex.reCLM.contDiff.comp s
  have si : ContDiff ℝ ∞ fi := Complex.imCLM.contDiff.comp s
  have hr : HasCompactSupport fr := h.comp_left (show (0:ℂ).re=0 from rfl)
  have hi : HasCompactSupport fi := h.comp_left (show (0:ℂ).im=0 from rfl)
  let reT := compactCoefficientTranslate fr sr.continuous hr
  let imT := compactCoefficientTranslate fi si.continuous hi
  obtain ⟨J,hJ⟩ := exists_bounded_coefficient_multiplier
  obtain ⟨R,_,cover⟩ := h.isBounded.subset_ball_lt 0 (0:ℂ)
  apply contDiff_iff_contDiffAt.mpr
  intro t0
  let r := R+‖t0‖+1
  let ex := diskConstantVector 0 r 1
  let ey := diskConstantVector 0 r I
  let approx := fun t => J (reT t) ex+J (imT t) ey
  have smooth : ContDiff ℝ ∞ approx :=
    ((J.contDiff.comp (smooth_compactCoefficientTranslate sr hr)).clm_apply contDiff_const).add
      ((J.contDiff.comp (smooth_compactCoefficientTranslate si hi)).clm_apply contDiff_const)
  apply smooth.contDiffAt.congr_of_eventuallyEq
  filter_upwards [ball_mem_nhds t0 zero_lt_one] with t near
  apply Lp.ext
  have trans := (measurePreserving_add_right volume t).quasiMeasurePreserving.ae_eq_comp rep
  filter_upwards [planeFieldTranslate_ae t b,trans,Lp.coeFn_add (J (reT t) ex) (J (imT t) ey),
    hJ (reT t) ex,hJ (imT t) ey,diskConstantVector_ae 0 r 1,diskConstantVector_ae 0 r I]
    with z hz hv add hx hy e1 e2
  change b (z+t)=f (z+t) at hv
  change planeFieldTranslate t b z=(J (reT t) ex+J (imT t) ey) z
  rw [hz,hv,add,Pi.add_apply,hx,hy,e1,e2]
  change f (z+t)=(f (z+t)).re • (ball (0:ℂ) r).indicator (fun _ => (1:ℂ)) z+
    (f (z+t)).im • (ball (0:ℂ) r).indicator (fun _ => I) z
  by_cases inside : z∈ball (0:ℂ) r
  · simp [inside]
  · have far : r≤‖z‖ := by simpa [mem_ball,dist_eq_norm] using inside
    have nt : ‖t‖<‖t0‖+1 := by
      have close := mem_ball.mp near
      rw [dist_eq_norm] at close
      have tri : ‖t‖≤‖t-t0‖+‖t0‖ := by simpa using norm_add_le (t-t0) t0
      linarith
    have out : z+t∉tsupport f := by
      intro m
      have small := cover m
      simp [mem_ball,dist_eq_norm] at small
      have tri : ‖z‖≤‖z+t‖+‖t‖ := by simpa using norm_sub_le (z+t) t
      dsimp [r] at far
      linarith
    simp [image_eq_zero_of_notMem_tsupport out,inside]
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_compact_field_translation
