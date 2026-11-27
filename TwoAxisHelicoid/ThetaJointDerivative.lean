import TwoAxisHelicoid.ThetaJointContinuity
import Mathlib.Analysis.Calculus.FDeriv.Partial

namespace TwoAxisHelicoid
set_option maxHeartbeats 1000000
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaJet thetaTerm

theorem thetaJet_joint_continuousAt {t : ℝ} (ht : 0 < t) (j : ℕ) (v : ℂ) :
    ContinuousAt (fun p : ℝ × ℂ => thetaJet p.1 j p.2) (t,v) := by
  have hp : 0 < t/2 := by positivity
  have h1 : ∀ᶠ p : ℝ × ℂ in 𝓝 (t,v), t/2 < p.1 :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds (by dsimp; linarith)
  have h2 : ∀ᶠ p : ℝ × ℂ in 𝓝 (t,v), |p.2.im| < |v.im|+1 :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by dsimp; linarith)
  exact (thetaJet_joint_continuousOn (y := |v.im|+1) hp j).continuousAt
    (Filter.mem_of_superset (h1.and h2) (fun _ h => ⟨h.1.le,h.2.le⟩))

noncomputable def thetaTimeCLM (t : ℝ) (j : ℕ) (v : ℂ) : ℝ →L[ℝ] ℂ :=
  (1 : ℝ →L[ℝ] ℝ).smulRight ((Real.pi/8 : ℂ)*(thetaJet t (j+2) v+thetaJet t j v))

noncomputable def thetaSpaceCLM (t : ℝ) (j : ℕ) (v : ℂ) : ℂ →L[ℝ] ℂ :=
  ((1 : ℂ →L[ℂ] ℂ).smulRight (thetaJet t (j+1) v)).restrictScalars ℝ

theorem thetaTimeCLM_continuousAt {t : ℝ} (ht : 0 < t) (j : ℕ) (v : ℂ) :
    ContinuousAt (fun p : ℝ × ℂ => thetaTimeCLM p.1 j p.2) (t,v) := by
  exact ((ContinuousLinearMap.smulRightL ℝ ℝ ℂ 1).continuous.continuousAt).comp
    (f := fun p : ℝ × ℂ => (Real.pi/8 : ℂ)*(thetaJet p.1 (j+2) p.2+thetaJet p.1 j p.2))
    (continuousAt_const.mul ((thetaJet_joint_continuousAt ht (j+2) v).add
      (thetaJet_joint_continuousAt ht j v)))

theorem thetaSpaceCLM_continuousAt {t : ℝ} (ht : 0 < t) (j : ℕ) (v : ℂ) :
    ContinuousAt (fun p : ℝ × ℂ => thetaSpaceCLM p.1 j p.2) (t,v) := by
  have h := ((ContinuousLinearMap.smulRightL ℂ ℂ ℂ 1).continuous.continuousAt).comp
    (f := fun p : ℝ × ℂ => thetaJet p.1 (j+1) p.2) (thetaJet_joint_continuousAt ht (j+1) v)
  exact (ContinuousLinearMap.restrictScalarsIsometry ℂ ℂ ℂ ℝ ℝ).continuous.continuousAt.comp
    (f := fun p : ℝ × ℂ => (1 : ℂ →L[ℂ] ℂ).smulRight (thetaJet p.1 (j+1) p.2)) h

theorem thetaJet_joint_hasStrictFDerivAt {t : ℝ} (ht : 0 < t) (j : ℕ) (v : ℂ) :
    HasStrictFDerivAt (fun p : ℝ × ℂ => thetaJet p.1 j p.2)
      ((thetaTimeCLM t j v).coprod (thetaSpaceCLM t j v)) (t,v) := by
  have hp : ∀ᶠ p : ℝ × ℂ in 𝓝 (t,v), 0 < p.1 :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds ht
  apply hasStrictFDerivAt_uncurry_coprod
    (𝕜 := ℝ) (u := (t,v))
    (f := fun t v => thetaJet t j v)
    (f₁ := fun t v => thetaTimeCLM t j v) (f₂ := fun t v => thetaSpaceCLM t j v)
  · filter_upwards [hp] with p hp
    exact (thetaJet_parameter_hasDerivAt hp j p.2).hasFDerivAt
  · filter_upwards [hp] with p hp
    exact (thetaJet_hasDerivAt hp j p.2).hasFDerivAt.restrictScalars ℝ
  · exact thetaTimeCLM_continuousAt ht j v
  · exact thetaSpaceCLM_continuousAt ht j v

theorem thetaJet_curve_hasDerivAt {u : ℝ → ℝ} {z : ℝ → ℂ} {s du : ℝ} {dz : ℂ}
    (hu : HasDerivAt u du s) (hz : HasDerivAt z dz s) (ht : 0 < u s) (j : ℕ) :
    HasDerivAt (fun r : ℝ => thetaJet (u r) j (z r))
      ((du : ℂ)*(Real.pi/8 : ℂ)*(thetaJet (u s) (j+2) (z s)+thetaJet (u s) j (z s))+
        dz*thetaJet (u s) (j+1) (z s)) s := by
  have hd := (thetaJet_joint_hasStrictFDerivAt ht j (z s)).hasFDerivAt.comp_hasDerivAt s
    (hu.prodMk hz)
  convert hd using 1
  · rfl
  · simp [thetaTimeCLM, thetaSpaceCLM, Complex.real_smul]
    ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaJet_curve_hasDerivAt
