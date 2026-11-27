import TwoAxisHelicoid.LocalMinimumLaplacian
import Mathlib.Topology.Order.Compact

namespace TwoAxisHelicoid
open Complex Filter Set Topology InnerProductSpace Laplacian
open scoped Topology InnerProductSpace

/-- Weak comparison against a strict positive barrier. This form permits
a bounded first-order and zeroth-order term. It is applied to nonnegative
differences of local sheets near first contact. -/
theorem analytic_plane_strict_barrier_comparison {S : Set ℂ} (hS : IsCompact S)
    (f v : ℂ → ℝ) {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε)
    (hf : ∀ z ∈ S, AnalyticAt ℝ f z) (hv : ∀ z ∈ S, AnalyticAt ℝ v z)
    (bdy : ∀ z ∈ S, z ∉ interior S → ε*v z ≤ f z)
    (sub : ∀ z ∈ interior S, (Δ f) z ≤ K*(|planePartial 1 f z|+|planePartial I f z|+f z))
    (strict : ∀ z ∈ interior S, K*(|planePartial 1 v z|+|planePartial I v z|+v z) < (Δ v) z) :
    ∀ z ∈ S, ε*v z ≤ f z := by
  let h := fun w => f w-ε*v w
  have ah (z : ℂ) (hz : z ∈ S) : AnalyticAt ℝ h z := (hf z hz).sub (analyticAt_const.mul (hv z hz))
  intro p hp
  by_contra! bad
  obtain ⟨z,hz,hm⟩ := hS.exists_isMinOn ⟨p,hp⟩ (fun w hw => (ah w hw).continuousAt.continuousWithinAt)
  have neg : h z < 0 := (hm hp).trans_lt (sub_neg.mpr bad)
  have hi : z ∈ interior S := by
    by_contra hn
    exact neg.not_ge (sub_nonneg.mpr (bdy z hz hn))
  have mine := hm.isLocalMin (mem_interior_iff_mem_nhds.mp hi)
  have grad (w : ℂ) : planePartial w f z=ε*planePartial w v z := by
    have d := ((hf z hz).differentiableAt.hasFDerivAt.sub ((hv z hz).differentiableAt.hasFDerivAt.const_smul ε)).fderiv
    change fderiv ℝ h z = _ at d
    have e := congrArg (fun D : ℂ →L[ℝ] ℝ => D w) (mine.fderiv_eq_zero.symm.trans d)
    change 0 = planePartial w f z-ε*planePartial w v z at e
    linarith
  have hcf : ContDiffAt ℝ 2 f z := (hf z hz).contDiffAt
  have hcv : ContDiffAt ℝ 2 v z := (hv z hz).contDiffAt
  have diff : (Δ h) z=(Δ f) z-ε*(Δ v) z :=
    (hcf.laplacian_sub (hcv.const_smul ε)).trans (congrArg (fun x : ℝ => (Δ f) z-x) (laplacian_smul ε hcv))
  have lap := analytic_plane_laplacian_nonnegative_at_minimum (ah z hz) mine
  rw [diff] at lap
  have est := sub z hi
  rw [grad 1,grad I,abs_mul,abs_mul,abs_of_pos hε] at est
  have gap := mul_lt_mul_of_pos_left (strict z hi) hε
  have val : f z < ε*v z := sub_neg.mp neg
  have mid := mul_le_mul_of_nonneg_left (show ε*|planePartial 1 v z|+ε*|planePartial I v z|+f z ≤
      ε*|planePartial 1 v z|+ε*|planePartial I v z|+ε*v z by linarith) hK
  nlinarith only [gap,est,mid,lap]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.analytic_plane_strict_barrier_comparison
