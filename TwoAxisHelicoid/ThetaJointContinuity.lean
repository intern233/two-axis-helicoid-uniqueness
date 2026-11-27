import TwoAxisHelicoid.RootVerticalRegular
import TwoAxisHelicoid.ThetaPeriodIntegral
import Mathlib.Analysis.Normed.Group.FunctionSeries

namespace TwoAxisHelicoid
open Set

theorem thetaJet_joint_continuousOn {tlo y : ℝ} (htlo : 0 < tlo) (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℂ => thetaJet p.1 j p.2)
      {p | tlo ≤ p.1 ∧ |p.2.im| ≤ y} := by
  unfold thetaJet
  apply continuousOn_tsum
    (fun n => (show Continuous (fun p : ℝ × ℂ => thetaTerm p.1 j n p.2) by
      unfold thetaTerm sineJet
      fun_prop).continuousOn)
    (thetaMajorant_summable htlo y j)
  intro n p hp
  exact thetaTerm_norm_le hp.1 hp.2 j n

theorem thetaJet_real_argument_continuousOn {tlo : ℝ} (htlo : 0 < tlo) (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => thetaJet p.1 j (Real.pi*p.2/2)) {p | tlo ≤ p.1} := by
  have hm : Continuous (fun p : ℝ × ℝ => (p.1, (Real.pi*p.2/2 : ℂ))) := by fun_prop
  apply (thetaJet_joint_continuousOn (y := 0) htlo j).comp hm.continuousOn
  intro p hp
  refine ⟨hp, ?_⟩
  simp

def rootRectangle : Set (ℝ × ℝ) :=
  Icc (rootTLower : ℝ) rootTUpper ×ˢ Icc (rootALower : ℝ) rootAUpper

theorem thetaG_rootRectangle_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => thetaG p.1 p.2) rootRectangle := by
  have hp : (0 : ℝ) < (rootTLower : ℝ) := by norm_num [rootTLower]
  have hsub : rootRectangle ⊆ {p : ℝ × ℝ | (rootTLower : ℝ) ≤ p.1} := fun _ h => h.1.1
  have h0 := (thetaJet_real_argument_continuousOn hp 0).mono hsub
  have h1 := (thetaJet_real_argument_continuousOn hp 1).mono hsub
  have h2 := (thetaJet_real_argument_continuousOn hp 2).mono hsub
  have hne : ∀ p ∈ rootRectangle, thetaJet p.1 0 (Real.pi*p.2/2) ≠ 0 := by
    intro p hp
    exact root_vertical_denominator hp.1.1 hp.1.2 hp.2.1 hp.2.2
  have htne : ∀ p ∈ rootRectangle, p.1 ≠ 0 := by
    intro p h
    exact ne_of_gt (hp.trans_le h.1.1)
  have ht : ContinuousOn (fun p : ℝ × ℝ => Real.pi/p.1) rootRectangle :=
    continuousOn_const.div continuous_fst.continuousOn htne
  exact (continuousOn_const.mul (((h1.div h0 hne).pow 2).sub (h2.div h0 hne))).sub
    (Complex.continuous_ofReal.comp_continuousOn ht)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaG_rootRectangle_continuousOn
