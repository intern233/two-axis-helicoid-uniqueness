import TwoAxisHelicoid.ComplexThetaJoint
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

theorem complexThetaDeriv_joint_continuousAt {t : ℂ} (ht : 0 < t.re) (j : ℕ) (v : ℂ) :
    ContinuousAt (fun p : ℂ × ℂ => (complexThetaTimeCLM p.1 j p.2).coprod
      (complexThetaSpaceCLM p.1 j p.2)) (t,v) := by
  have htime : ContinuousAt (fun p : ℂ × ℂ => complexThetaTimeCLM p.1 j p.2) (t,v) :=
    (ContinuousLinearMap.smulRightL ℂ ℂ ℂ 1).continuous.continuousAt.comp
      (f := fun p : ℂ × ℂ => (Real.pi/8:ℂ)*(complexThetaJet p.1 (j+2) p.2+complexThetaJet p.1 j p.2))
      (continuousAt_const.mul ((complexThetaJet_joint_continuousAt ht (j+2) v).add
        (complexThetaJet_joint_continuousAt ht j v)))
  have hspace : ContinuousAt (fun p : ℂ × ℂ => complexThetaSpaceCLM p.1 j p.2) (t,v) :=
    (ContinuousLinearMap.smulRightL ℂ ℂ ℂ 1).continuous.continuousAt.comp
      (f := fun p : ℂ × ℂ => complexThetaJet p.1 (j+1) p.2)
      (complexThetaJet_joint_continuousAt ht (j+1) v)
  exact htime.continuousLinearMapCoprod hspace

theorem complexThetaJet_contDiffAt_one {t : ℂ} (ht : 0 < t.re) (j : ℕ) (v : ℂ) :
    ContDiffAt ℂ 1 (fun p : ℂ × ℂ => complexThetaJet p.1 j p.2) (t,v) := by
  apply contDiffAt_one_iff.mpr
  refine ⟨fun p => (complexThetaTimeCLM p.1 j p.2).coprod (complexThetaSpaceCLM p.1 j p.2),
    {p : ℂ × ℂ | 0 < p.1.re},(isOpen_lt continuous_const (by fun_prop)).mem_nhds ht,?_,?_⟩
  · intro p hp
    exact (complexThetaDeriv_joint_continuousAt hp j p.2).continuousWithinAt
  · intro p hp
    exact (complexThetaJet_joint_hasStrictFDerivAt hp j p.2).hasFDerivAt

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.complexThetaJet_contDiffAt_one
