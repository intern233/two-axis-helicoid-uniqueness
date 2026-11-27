import TwoAxisHelicoid.ComplexThetaSeries
import Mathlib.Analysis.Calculus.FDeriv.Partial

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] complexThetaJet

noncomputable def complexThetaTimeCLM (t : ℂ) (j : ℕ) (v : ℂ) : ℂ →L[ℂ] ℂ :=
  (1:ℂ →L[ℂ] ℂ).smulRight ((Real.pi/8:ℂ)*(complexThetaJet t (j+2) v+complexThetaJet t j v))

noncomputable def complexThetaSpaceCLM (t : ℂ) (j : ℕ) (v : ℂ) : ℂ →L[ℂ] ℂ :=
  (1:ℂ →L[ℂ] ℂ).smulRight (complexThetaJet t (j+1) v)

theorem complexThetaJet_joint_hasStrictFDerivAt {t : ℂ} (ht : 0 < t.re) (j : ℕ) (v : ℂ) :
    HasStrictFDerivAt (fun p : ℂ × ℂ => complexThetaJet p.1 j p.2)
      ((complexThetaTimeCLM t j v).coprod (complexThetaSpaceCLM t j v)) (t,v) := by
  have hp : ∀ᶠ p : ℂ × ℂ in 𝓝 (t,v), 0 < p.1.re :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds ht
  apply hasStrictFDerivAt_uncurry_coprod
    (𝕜 := ℂ) (u := (t,v)) (f := fun t v => complexThetaJet t j v)
    (f₁ := fun t v => complexThetaTimeCLM t j v) (f₂ := fun t v => complexThetaSpaceCLM t j v)
  · filter_upwards [hp] with p hp
    exact (complexThetaJet_time_hasDerivAt hp j p.2).hasFDerivAt
  · filter_upwards [hp] with p hp
    exact (complexThetaJet_space_hasDerivAt hp j p.2).hasFDerivAt
  · exact (ContinuousLinearMap.smulRightL ℂ ℂ ℂ 1).continuous.continuousAt.comp
      (f := fun p : ℂ × ℂ => (Real.pi/8:ℂ)*(complexThetaJet p.1 (j+2) p.2+complexThetaJet p.1 j p.2))
      (continuousAt_const.mul ((complexThetaJet_joint_continuousAt ht (j+2) v).add
        (complexThetaJet_joint_continuousAt ht j v)))
  · exact (ContinuousLinearMap.smulRightL ℂ ℂ ℂ 1).continuous.continuousAt.comp
      (f := fun p : ℂ × ℂ => complexThetaJet p.1 (j+1) p.2)
      (complexThetaJet_joint_continuousAt ht (j+1) v)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.complexThetaJet_joint_hasStrictFDerivAt
