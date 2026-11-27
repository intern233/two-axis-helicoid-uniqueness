import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
set_option maxHeartbeats 0

/-- The quotient extended at simple zeros by the quotient of derivatives. -/
noncomputable def analyticSimpleQuotient (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  if g z = 0 then deriv f z / deriv g z else f z / g z

theorem analyticSimpleQuotient_mul {f g : ℂ → ℂ}
    (hz : ∀ z, g z = 0 → f z = 0) (z : ℂ) :
    analyticSimpleQuotient f g z * g z = f z := by
  by_cases h : g z = 0
  · simp [analyticSimpleQuotient, h, hz z h]
  · simp [analyticSimpleQuotient, h]

theorem analyticSimpleQuotient_differentiable {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hz : ∀ z, g z = 0 → f z = 0)
    (hs : ∀ z, g z = 0 → deriv g z ≠ 0) :
    Differentiable ℂ (analyticSimpleQuotient f g) := by
  intro z
  by_cases hgz : g z = 0
  · have hdf : Differentiable ℂ (dslope f z) := differentiableOn_univ.mp
      ((Complex.differentiableOn_dslope (by simp : (univ : Set ℂ) ∈ 𝓝 z)).mpr
        hf.differentiableOn)
    have hdg : Differentiable ℂ (dslope g z) := differentiableOn_univ.mp
      ((Complex.differentiableOn_dslope (by simp : (univ : Set ℂ) ∈ 𝓝 z)).mpr
        hg.differentiableOn)
    have hsn : dslope g z z ≠ 0 := by simpa only [dslope_same] using hs z hgz
    apply ((hdf z).div (hdg z) hsn).congr_of_eventuallyEq
    filter_upwards [(hdg z).continuousAt.eventually_ne hsn] with w hw
    by_cases he : w = z
    · subst w
      simp [analyticSimpleQuotient, hgz, dslope_same]
    · have hgw : g w ≠ 0 := by
        have h := sub_smul_dslope g z w
        simp only [smul_eq_mul, hgz, sub_zero] at h
        rw [← h]
        exact mul_ne_zero (sub_ne_zero.mpr he) hw
      simp only [analyticSimpleQuotient, ite_eq_right hgw, Pi.div_apply, dslope_of_ne _ he,
        slope, smul_eq_mul, vsub_eq_sub, hgz, hz z hgz, sub_zero]
      field_simp
  · apply ((hf z).div (hg z) hgz).congr_of_eventuallyEq
    filter_upwards [(hg z).continuousAt.eventually_ne hgz] with w hw
    simp only [analyticSimpleQuotient, ite_eq_right hw, Pi.div_apply]

theorem deriv_shift_of_common_multiplier {f c : ℂ → ℂ} (p : ℂ)
    (hf : Differentiable ℂ f) (hc : Differentiable ℂ c)
    (he : ∀ z, f (z+p) = c z*f z) {z : ℂ} (hz : f z = 0) :
    deriv f (z+p) = c z * deriv f z := by
  have hl := (hf (z+p)).hasDerivAt.comp z ((hasDerivAt_id z).add_const p)
  have hr := ((hc z).hasDerivAt.mul (hf z).hasDerivAt).congr_of_eventuallyEq
    (Eventually.of_forall he)
  have h := hl.unique hr
  simpa only [mul_one, hz, mul_zero, zero_add] using h

theorem analyticSimpleQuotient_periodic {f g c : ℂ → ℂ} (p : ℂ)
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hc : Differentiable ℂ c) (hc0 : ∀ z, c z ≠ 0)
    (hfg : ∀ z, g z = 0 → f z = 0)
    (hF : ∀ z, f (z+p) = c z*f z) (hG : ∀ z, g (z+p) = c z*g z) :
    Function.Periodic (analyticSimpleQuotient f g) p := by
  intro z
  by_cases hz : g z = 0
  · have hzp : g (z+p) = 0 := by rw [hG, hz, mul_zero]
    simp only [analyticSimpleQuotient, ite_eq_left hz, ite_eq_left hzp,
      deriv_shift_of_common_multiplier p hf hc hF (hfg z hz),
      deriv_shift_of_common_multiplier p hg hc hG hz]
    exact mul_div_mul_left _ _ (hc0 z)
  · have hzp : g (z+p) ≠ 0 := by rw [hG]; exact mul_ne_zero (hc0 z) hz
    simp only [analyticSimpleQuotient, ite_eq_right hz, ite_eq_right hzp]
    rw [hF, hG]
    exact mul_div_mul_left _ _ (hc0 z)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.analyticSimpleQuotient_differentiable
#print axioms TwoAxisHelicoid.analyticSimpleQuotient_periodic
