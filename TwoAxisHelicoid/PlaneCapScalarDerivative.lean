import TwoAxisHelicoid.SmoothPlaneCap
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace TwoAxisHelicoid
open Real Set Filter
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

theorem planeCapSwitch_contDiff (A : ℝ) : ContDiff ℝ (∞ : WithTop ℕ∞) (planeCapSwitch A) := by
  unfold planeCapSwitch
  fun_prop

theorem planeCapSwitch_hasDerivAt (A q : ℝ) :
    HasDerivAt (planeCapSwitch A) (deriv (planeCapSwitch A) q) q :=
  ((planeCapSwitch_contDiff A).differentiable (by simp) q).hasDerivAt

theorem planeCapSwitch_deriv_nonneg (A q : ℝ) : 0 ≤ deriv (planeCapSwitch A) q :=
  (planeCapSwitch_monotone A).deriv_nonneg

theorem planeCapSwitch_deriv_zero {A q : ℝ} (hq : q ≤ A) : deriv (planeCapSwitch A) q = 0 := by
  apply IsLocalMin.deriv_eq_zero
  filter_upwards [] with r
  rw [planeCapSwitch_zero hq]
  exact planeCapSwitch_nonneg A r

theorem planeCapScale_hasDerivAt {A H q : ℝ} (hq : 0 ≤ q) :
    HasDerivAt (planeCapScale A H)
      (-deriv (planeCapSwitch A) q+
        ((deriv (planeCapSwitch A) q*H)*(1+q)-planeCapSwitch A q*H)/(1+q)^2) q := by
  have hden : 1+q ≠ 0 := by positivity
  have hχ := planeCapSwitch_hasDerivAt A q
  convert! ((hasDerivAt_const q 1).sub hχ).add
    ((hχ.mul_const H).div ((hasDerivAt_const q 1).add (hasDerivAt_id q)) hden) using 1
  simp

theorem planeCapHeight_hasDerivAt {A H q : ℝ} (hq : 0 ≤ q) :
    HasDerivAt (planeCapHeight A H)
      (H*(deriv (planeCapSwitch A) q*(q/(1+q))+planeCapSwitch A q*(1/(1+q)^2))) q := by
  have hden : 1+q ≠ 0 := by positivity
  have hf : HasDerivAt (fun r : ℝ => r/(1+r)) (1/(1+q)^2) q := by
    convert! (hasDerivAt_id q).div ((hasDerivAt_const q 1).add (hasDerivAt_id q)) hden using 1
    simp
  exact ((planeCapSwitch_hasDerivAt A q).mul hf).const_mul H

theorem planeCapScale_deriv_zero {A H q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ A) :
    deriv (planeCapScale A H) q = 0 := by
  rw [(planeCapScale_hasDerivAt (A := A) (H := H) hq0).deriv,
    planeCapSwitch_zero hq,planeCapSwitch_deriv_zero hq]
  simp

theorem planeCapHeight_deriv_zero {A H q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ A) :
    deriv (planeCapHeight A H) q = 0 := by
  rw [(planeCapHeight_hasDerivAt (A := A) (H := H) hq0).deriv,
    planeCapSwitch_zero hq,planeCapSwitch_deriv_zero hq]
  simp

theorem planeCapHeight_deriv_pos {A H q : ℝ} (hA : 0 ≤ A) (hH : 0 < H) (hq : A < q) :
    0 < deriv (planeCapHeight A H) q := by
  have hq0 : 0 < q := hA.trans_lt hq
  rw [(planeCapHeight_hasDerivAt (A := A) (H := H) hq0.le).deriv]
  apply mul_pos hH
  apply add_pos_of_nonneg_of_pos
  · exact mul_nonneg (planeCapSwitch_deriv_nonneg A q) (by positivity)
  · exact mul_pos (planeCapSwitch_pos hq) (by positivity)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.planeCapHeight_deriv_pos
#print axioms TwoAxisHelicoid.planeCapScale_deriv_zero
