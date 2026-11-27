import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

namespace TwoAxisHelicoid
open Set Real
open scoped ContDiff

/-- Smoothly collapse an inner boundary radius to zero while keeping
every radius in a prescribed outer collar fixed. -/
theorem smooth_annular_radius {r s : ℝ} (hr : 0≤r) (rs : r<s) :
    ∃ e : ℝ ≃o ℝ, e r=0 ∧ (∀ x, s≤x → e x=x) ∧
      ContDiff ℝ ∞ (e : ℝ → ℝ) ∧ ContDiff ℝ ∞ (e.symm : ℝ → ℝ) := by
  let b := fun x : ℝ => smoothTransition ((x-r)/(s-r))
  let g := fun x : ℝ => r*b x
  let f := fun x : ℝ => x-r+g x
  have bp : 0<s-r := sub_pos.mpr rs
  have bm : Monotone b := fun _ _ h => smoothTransition.monotone (div_le_div_of_nonneg_right (sub_le_sub_right h r) bp.le)
  have gm : Monotone g := fun _ _ h => mul_le_mul_of_nonneg_left (bm h) hr
  have gs : ContDiff ℝ ∞ g := contDiff_const.mul (smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _))
  have fs : ContDiff ℝ ∞ f := (contDiff_id.sub contDiff_const).add gs
  have mono : StrictMono f := fun _ _ h => add_lt_add_of_lt_of_le (sub_lt_sub_right h r) (gm h.le)
  have onto : Function.Surjective f := by
    intro y
    have small : f y≤y := by
      dsimp only [f,g]
      linarith [mul_le_mul_of_nonneg_left (show b y≤1 from smoothTransition.le_one _) hr]
    have large : y≤f (y+r) := by
      dsimp only [f,g]
      linarith [mul_nonneg hr (show 0≤b (y+r) from smoothTransition.nonneg _)]
    obtain ⟨x,_,eq⟩ := intermediate_value_Icc (show y≤y+r by linarith) fs.continuous.continuousOn ⟨small,large⟩
    exact ⟨x,eq⟩
  let e := mono.orderIsoOfSurjective f onto
  have shift (x : ℝ) : HasDerivAt f (1+deriv g x) x := by
    change HasDerivAt (fun y : ℝ => y-r+g y) (1+deriv g x) x
    exact ((hasDerivAt_id x).sub_const r).fun_add ((gs.differentiable (by simp) x).hasDerivAt)
  have ei : ContDiff ℝ ∞ (e.symm : ℝ → ℝ) := e.toHomeomorph.contDiff_symm_deriv
    (fun x => (add_pos_of_pos_of_nonneg zero_lt_one (gm.deriv_nonneg (x:=x))).ne') shift fs
  refine ⟨e,?_,?_,fs,ei⟩
  · change r-r+r*smoothTransition ((r-r)/(s-r))=0
    simp [smoothTransition.zero_of_nonpos]
  · intro x hx
    change x-r+r*smoothTransition ((x-r)/(s-r))=x
    rw [smoothTransition.one_of_one_le ((le_div_iff₀ bp).mpr (by linarith))]
    ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_annular_radius

