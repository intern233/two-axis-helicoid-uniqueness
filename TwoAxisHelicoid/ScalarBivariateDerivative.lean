import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace TwoAxisHelicoid
open Filter
open scoped Topology

theorem scalar_bivariate_curve_hasDerivAt {F Ft Fa : ℝ → ℝ → ℝ}
    {u a : ℝ → ℝ} {s du da : ℝ}
    (hdt : ∀ᶠ p : ℝ × ℝ in 𝓝 (u s,a s), HasDerivAt (fun t => F t p.2) (Ft p.1 p.2) p.1)
    (hda : ∀ᶠ p : ℝ × ℝ in 𝓝 (u s,a s), HasDerivAt (F p.1) (Fa p.1 p.2) p.2)
    (hct : ContinuousAt (fun p : ℝ × ℝ => Ft p.1 p.2) (u s,a s))
    (hca : ContinuousAt (fun p : ℝ × ℝ => Fa p.1 p.2) (u s,a s))
    (hu : HasDerivAt u du s) (ha : HasDerivAt a da s) :
    HasDerivAt (fun r => F (u r) (a r)) (du*Ft (u s) (a s)+da*Fa (u s) (a s)) s := by
  let f1 : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun t b => (1 : ℝ →L[ℝ] ℝ).smulRight (Ft t b)
  let f2 : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun t b => (1 : ℝ →L[ℝ] ℝ).smulRight (Fa t b)
  have hd1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (u s,a s), HasFDerivAt (fun t => F t p.2) (f1 p.1 p.2) p.1 :=
    hdt.mono (fun _ h => h.hasFDerivAt)
  have hd2 : ∀ᶠ p : ℝ × ℝ in 𝓝 (u s,a s), HasFDerivAt (F p.1) (f2 p.1 p.2) p.2 :=
    hda.mono (fun _ h => h.hasFDerivAt)
  have hc1 : ContinuousAt (fun p : ℝ × ℝ => f1 p.1 p.2) (u s,a s) :=
    (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous.continuousAt.comp
      (f := fun p : ℝ × ℝ => Ft p.1 p.2) hct
  have hc2 : ContinuousAt (fun p : ℝ × ℝ => f2 p.1 p.2) (u s,a s) :=
    (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous.continuousAt.comp
      (f := fun p : ℝ × ℝ => Fa p.1 p.2) hca
  have hd := (hasStrictFDerivAt_uncurry_coprod (u := (u s,a s)) (f := F) (f₁ := f1) (f₂ := f2) hd1 hd2 hc1 hc2).hasFDerivAt.comp_hasDerivAt s (hu.prodMk ha)
  convert hd using 1
  · rfl
  · rfl

end TwoAxisHelicoid
