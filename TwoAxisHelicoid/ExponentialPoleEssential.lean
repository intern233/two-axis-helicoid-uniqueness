import TwoAxisHelicoid.HeightGaussEndNormalForm
import Mathlib.Analysis.Meromorphic.LogDeriv

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- The exponential of a nonzero reciprocal cannot be meromorphic at
the origin. Its logarithmic derivative has a double pole, whereas
that of a nonzero meromorphic germ has at most a simple pole. -/
theorem exp_reciprocal_not_meromorphic {c : ℂ} (hc : c≠0) :
    ¬ MeromorphicAt (fun z : ℂ => exp (c/z)) 0 := by
  let f := fun z : ℂ => exp (c/z)
  have eq : logDeriv f =ᶠ[𝓝[≠] (0:ℂ)] fun z => -c/z^2+0 := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    change z≠0 at hz
    have hd : HasDerivAt (fun w : ℂ => c/w) (-c/z^2) z := by
      simpa [Pi.div_apply] using! (hasDerivAt_const z c).div (hasDerivAt_id z) hz
    change deriv f z/f z=_
    rw [hd.cexp.deriv,add_zero]
    dsimp [f]
    field_simp
  have order := (analytic_double_pole_with_remainder (neg_ne_zero.mpr hc) (k := fun _ => 0) analyticAt_const eq).2
  intro hm
  by_cases zero : meromorphicOrderAt f 0=0
  · have h := meromorphicOrderAt_logDeriv_nonneg hm zero
    rw [order] at h
    exact (by decide : ¬ (0:ℤ) ≤ -2) (WithTop.coe_le_coe.mp h)
  have finite : meromorphicOrderAt f 0≠⊤ := by
    intro h
    obtain ⟨w,hw⟩ := (meromorphicOrderAt_eq_top_iff.mp h).exists
    exact exp_ne_zero _ hw
  have e := meromorphicOrderAt_logDeriv_eq_neg_one hm zero finite
  rw [order] at e
  norm_num at e

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exp_reciprocal_not_meromorphic
