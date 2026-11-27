import TwoAxisHelicoid.PlaneGradientTranslations
import Mathlib.Analysis.Distribution.TemperedDistribution

namespace TwoAxisHelicoid
open MeasureTheory Complex TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv

theorem plane_translate_distribution_test (u : Lp ℂ 2 (volume : Measure ℂ)) (t : ℂ) (φ : 𝓢(ℂ, ℂ)) :
    (Lp.toTemperedDistribution (planeFieldTranslate t u)) φ =
      (Lp.toTemperedDistribution u) (φ.compSubConstCLM ℂ t) := by
  rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
  let g := fun z : ℂ => φ (z-t) • u z
  calc
    _ = (∫ z : ℂ, g (z+t)) := by
      apply integral_congr_ae
      filter_upwards [planeFieldTranslate_ae t u] with z h
      simp only [g,h,add_sub_cancel_right]
    _ = _ := integral_add_right_eq_self _ _

/-- The actual L² translation of a weak Laplacian is the weak Laplacian
of the translated field on the entire plane. -/
theorem plane_laplacian_translate (u v : Lp ℂ 2 (volume : Measure ℂ)) {t : ℂ}
    (h : Δ (u : 𝓢'(ℂ, ℂ)) = (v : 𝓢'(ℂ, ℂ))) :
    Δ ((planeFieldTranslate t u) : 𝓢'(ℂ, ℂ)) = ((planeFieldTranslate t v) : 𝓢'(ℂ, ℂ)) := by
  let T := SchwartzMap.compSubConstCLM ℂ t (F:=ℂ)
  have der (φ : 𝓢(ℂ, ℂ)) (d : ℂ) : ∂_{d} (T φ)=T (∂_{d} φ) := by
    ext z
    simp only [T,SchwartzMap.lineDerivOp_apply_eq_fderiv,SchwartzMap.compSubConstCLM_apply]
    change fderiv ℝ (fun x : ℂ => φ (x-t)) z d = fderiv ℝ (⇑φ) (z-t) d
    simpa only [sub_eq_add_neg] using congrArg (fun l : ℂ →L[ℝ] ℂ => l d)
      (fderiv_comp_add_right (𝕜:=ℝ) (f:=⇑φ) (a:=-t) (x:=z))
  have lap (φ : 𝓢(ℂ, ℂ)) : Δ (T φ) = T (Δ φ) := by
    let b := stdOrthonormalBasis ℝ ℂ
    rw [SchwartzMap.laplacian_eq_sum b,SchwartzMap.laplacian_eq_sum b,map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [der,der]
  ext φ
  rw [TemperedDistribution.laplacian_apply_apply,plane_translate_distribution_test,plane_translate_distribution_test]
  change (Lp.toTemperedDistribution u) (T (Δ φ))=(Lp.toTemperedDistribution v) (T φ)
  rw [←lap]
  simpa only [TemperedDistribution.laplacian_apply_apply] using congrArg (fun W : 𝓢'(ℂ, ℂ) => W (T φ)) h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.plane_laplacian_translate

