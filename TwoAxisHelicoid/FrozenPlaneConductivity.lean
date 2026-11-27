module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

public section

namespace TwoAxisHelicoid
open Complex Set Metric
open scoped ContDiff

@[expose] noncomputable def planeFreezeCutoff : ContDiffBump (0 : ℝ × ℂ) :=
  ⟨1,2,by norm_num,by norm_num⟩

@[expose] noncomputable def planeFreezePerturbation (F : ℂ → ℝ) (p : ℂ) (x : ℝ × ℂ) : ℝ :=
  planeFreezeCutoff x * (F (p+x.1 • x.2)-F p)

@[expose] noncomputable def planeFrozenCoefficient (F : ℂ → ℝ) (p : ℂ) (s : ℝ) (z : ℂ) : ℝ :=
  F p + planeFreezePerturbation F p (s,z)

theorem planeFreezePerturbation_smooth {F : ℂ → ℝ} (h : ContDiff ℝ ∞ F) (p : ℂ) :
    ContDiff ℝ ∞ (planeFreezePerturbation F p) :=
  planeFreezeCutoff.contDiff.mul ((h.comp (contDiff_const.add (contDiff_fst.smul contDiff_snd))).sub contDiff_const)

theorem planeFreezePerturbation_compact (F : ℂ → ℝ) (p : ℂ) :
    HasCompactSupport (planeFreezePerturbation F p) :=
  planeFreezeCutoff.hasCompactSupport.mul_right

theorem planeFrozenCoefficient_smooth {F : ℂ → ℝ} (h : ContDiff ℝ ∞ F) (p : ℂ) (s : ℝ) :
    ContDiff ℝ ∞ (planeFrozenCoefficient F p s) :=
  contDiff_const.add ((planeFreezePerturbation_smooth h p).comp (contDiff_const.prodMk contDiff_id))

@[simp] theorem planeFrozenCoefficient_zero (F : ℂ → ℝ) (p z : ℂ) :
    planeFrozenCoefficient F p 0 z = F p := by
  simp [planeFrozenCoefficient,planeFreezePerturbation]

theorem planeFrozenCoefficient_core (F : ℂ → ℝ) (p : ℂ) {s : ℝ} {z : ℂ}
    (hs : ‖s‖≤1) (hz : ‖z‖≤1) : planeFrozenCoefficient F p s z=F (p+s • z) := by
  have m : (s,z)∈closedBall (0 : ℝ × ℂ) planeFreezeCutoff.rIn := by
    change dist (s,z) 0≤1
    simpa only [dist_zero_right,Prod.norm_def,max_le_iff] using And.intro hs hz
  simp [planeFrozenCoefficient,planeFreezePerturbation,planeFreezeCutoff.one_of_mem_closedBall m]

/-- Freezing at a prescribed point and rescaling preserves a common ellipticity
constant through the interpolation, including its transition annulus. -/
theorem planeFrozenCoefficient_lower (A B C : ℂ → ℝ) (p : ℂ) {k : ℝ}
    (low : ∀ z x y, (x^2+y^2)/k≤C z*x^2-2*B z*x*y+A z*y^2)
    (s : ℝ) (z : ℂ) (x y : ℝ) :
    (x^2+y^2)/k ≤ planeFrozenCoefficient C p s z*x^2 -
      2*planeFrozenCoefficient B p s z*x*y + planeFrozenCoefficient A p s z*y^2 := by
  let θ := planeFreezeCutoff (s,z)
  have pos : 0≤θ := planeFreezeCutoff.nonneg
  have upper : 0≤1-θ := sub_nonneg.mpr planeFreezeCutoff.le_one
  have a := mul_le_mul_of_nonneg_left (low p x y) upper
  have b := mul_le_mul_of_nonneg_left (low (p+s • z) x y) pos
  change _≤(C p+θ*(C (p+s • z)-C p))*x^2 -
    2*(B p+θ*(B (p+s • z)-B p))*x*y+(A p+θ*(A (p+s • z)-A p))*y^2
  linear_combination (norm := ring_nf) a+b
  exact le_rfl
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.planeFrozenCoefficient_lower
