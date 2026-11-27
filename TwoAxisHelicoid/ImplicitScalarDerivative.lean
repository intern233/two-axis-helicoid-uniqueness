import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace TwoAxisHelicoid
open Filter
open scoped Topology

/-- The derivative of an already specified continuous implicit branch. The branch
is identified with the implicit-function-theorem germ, rather than assumed smooth. -/
theorem implicit_scalar_hasDerivAt {F Ft Fa : ℝ → ℝ → ℝ} {a : ℝ → ℝ} {t : ℝ}
    (hdt : ∀ᶠ p : ℝ × ℝ in 𝓝 (t,a t), HasDerivAt (fun s => F s p.2) (Ft p.1 p.2) p.1)
    (hda : ∀ᶠ p : ℝ × ℝ in 𝓝 (t,a t), HasDerivAt (F p.1) (Fa p.1 p.2) p.2)
    (hct : ContinuousAt (fun p : ℝ × ℝ => Ft p.1 p.2) (t,a t))
    (hca : ContinuousAt (fun p : ℝ × ℝ => Fa p.1 p.2) (t,a t))
    (hn : Fa t (a t) ≠ 0) (hbranch : ContinuousAt a t)
    (hzero : ∀ᶠ s in 𝓝 t, F s (a s) = 0) :
    HasDerivAt a (-Ft t (a t)/Fa t (a t)) t := by
  let f1 : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun s b => (1 : ℝ →L[ℝ] ℝ).smulRight (Ft s b)
  let f2 : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun s b => (1 : ℝ →L[ℝ] ℝ).smulRight (Fa s b)
  have hd1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (t,a t), HasFDerivAt (fun s => F s p.2) (f1 p.1 p.2) p.1 :=
    hdt.mono (fun _ h => h.hasFDerivAt)
  have hd2 : ∀ᶠ p : ℝ × ℝ in 𝓝 (t,a t), HasFDerivAt (F p.1) (f2 p.1 p.2) p.2 :=
    hda.mono (fun _ h => h.hasFDerivAt)
  have hc1 : ContinuousAt (fun p : ℝ × ℝ => f1 p.1 p.2) (t,a t) :=
    (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous.continuousAt.comp
      (f := fun p : ℝ × ℝ => Ft p.1 p.2) hct
  have hc2 : ContinuousAt (fun p : ℝ × ℝ => f2 p.1 p.2) (t,a t) :=
    (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous.continuousAt.comp
      (f := fun p : ℝ × ℝ => Fa p.1 p.2) hca
  have hinv : (f2 t (a t)).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hn),?_⟩
    apply ContinuousLinearMap.ext
    intro x
    simp [f2, ContinuousLinearEquiv.unitsEquivAut_apply]
  let ψ := implicitFunctionOfBivariate hd1 hd2 hc1 hc2 hinv
  have hψ := (hasStrictFDerivAt_implicitFunctionOfBivariate hd1 hd2 hc1 hc2 hinv).hasFDerivAt.differentiableAt
  have hrel := eventually_apply_eq_iff_implicitFunctionOfBivariate hd1 hd2 hc1 hc2 hinv
  have hrel' := (continuousAt_id.prodMk hbranch).eventually hrel
  have hf0 : F t (a t) = 0 := hzero.self_of_nhds
  have heq : ψ =ᶠ[𝓝 t] a := by
    filter_upwards [hrel',hzero] with s hs hz
    exact hs.mp (hz.trans hf0.symm)
  have hdiff : DifferentiableAt ℝ a t := hψ.congr_of_eventuallyEq heq.symm
  have hf := (hasStrictFDerivAt_uncurry_coprod (u := (t,a t)) (f := F) (f₁ := f1) (f₂ := f2) hd1 hd2 hc1 hc2).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk hdiff.hasDerivAt)
  have hz : HasDerivAt (fun s => F s (a s)) 0 t :=
    (hasDerivAt_const t 0).congr_of_eventuallyEq hzero
  have hder := hf.unique hz
  have hsum : Ft t (a t)+deriv a t*Fa t (a t) = 0 := by
    change 1*Ft t (a t)+deriv a t*Fa t (a t) = 0 at hder
    simpa only [one_mul] using hder
  have hslope : deriv a t = -Ft t (a t)/Fa t (a t) := by
    apply (eq_div_iff hn).mpr
    linarith
  simpa only [hslope] using hdiff.hasDerivAt

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.implicit_scalar_hasDerivAt
