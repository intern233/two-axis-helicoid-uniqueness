import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology

/-- The actual scalar fiber map used to straighten a small normal graph. -/
noncomputable def scalarFiberShift (χ : ℝ → ℝ) (d s : ℝ) : ℝ := s+χ s*d

theorem scalarFiberShift_hasDerivAt {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) (d s : ℝ) :
    HasDerivAt (scalarFiberShift χ d) (1+deriv χ s*d) s :=
  (hasDerivAt_id s).add ((hχ s).hasDerivAt.mul_const d)

theorem scalarFiberShift_strictMono {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ)
    {C d : ℝ} (hbound : ∀ s, |deriv χ s| ≤ C) (hsmall : |d| *C < 1) :
    StrictMono (scalarFiberShift χ d) := by
  apply strictMono_of_hasDerivAt_pos (scalarFiberShift_hasDerivAt hχ d)
  intro s
  have he : |deriv χ s*d| < 1 := by
    rw [abs_mul,mul_comm]
    exact (mul_le_mul_of_nonneg_left (hbound s) (abs_nonneg d)).trans_lt hsmall
  have hlo := (abs_lt.mp he).1
  linarith

theorem scalarFiberShift_eq_self {χ : ℝ → ℝ} {R d s : ℝ}
    (hsupport : ∀ x, R ≤ |x| → χ x = 0) (hs : R ≤ |s|) :
    scalarFiberShift χ d s = s := by
  simp only [scalarFiberShift,hsupport s hs,zero_mul,add_zero]

theorem scalarFiberShift_surjective {χ : ℝ → ℝ} (hχ : Continuous χ) {R : ℝ}
    (hsupport : ∀ s, R ≤ |s| → χ s = 0) (d : ℝ) :
    Function.Surjective (scalarFiberShift χ d) := by
  have hc : Continuous (scalarFiberShift χ d) := continuous_id.add (hχ.mul continuous_const)
  apply hc.surjective
  · apply tendsto_id.congr'
    filter_upwards [eventually_ge_atTop R] with s hs
    exact (scalarFiberShift_eq_self hsupport (hs.trans (le_abs_self s))).symm
  · apply tendsto_id.congr'
    filter_upwards [eventually_le_atBot (-R)] with s hs
    have hb : R ≤ |s| := by linarith [neg_le_abs s]
    exact (scalarFiberShift_eq_self hsupport hb).symm

theorem scalarFiberShift_bijective {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ)
    {C d R : ℝ} (hbound : ∀ s, |deriv χ s| ≤ C) (hsmall : |d| *C < 1)
    (hsupport : ∀ s, R ≤ |s| → χ s = 0) : Function.Bijective (scalarFiberShift χ d) :=
  ⟨(scalarFiberShift_strictMono hχ hbound hsmall).injective,
    scalarFiberShift_surjective hχ.continuous hsupport d⟩

theorem scalarFiberShift_preserves_strip {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ)
    {C d R : ℝ} (hR : 0 < R) (hbound : ∀ s, |deriv χ s| ≤ C) (hsmall : |d| *C < 1)
    (hsupport : ∀ s, R ≤ |s| → χ s = 0) (s : ℝ) :
    |scalarFiberShift χ d s| < R ↔ |s| < R := by
  have hm := scalarFiberShift_strictMono hχ hbound hsmall
  have hleft : scalarFiberShift χ d (-R) = -R :=
    scalarFiberShift_eq_self hsupport (by rw [abs_neg,abs_of_pos hR])
  have hright : scalarFiberShift χ d R = R :=
    scalarFiberShift_eq_self hsupport (by rw [abs_of_pos hR])
  calc
    |scalarFiberShift χ d s| < R ↔
        scalarFiberShift χ d (-R) < scalarFiberShift χ d s ∧
          scalarFiberShift χ d s < scalarFiberShift χ d R := by rw [hleft,hright,abs_lt]
    _ ↔ -R < s ∧ s < R := and_congr hm.lt_iff_lt hm.lt_iff_lt
    _ ↔ |s| < R := abs_lt.symm

theorem scalarFiberShift_zero (χ : ℝ → ℝ) (d : ℝ) (hχ : χ 0 = 1) :
    scalarFiberShift χ d 0 = d := by simp only [scalarFiberShift,hχ,one_mul,zero_add]

theorem scalarFiberShift_time_bound {C d time : ℝ}
    (hsmall : |d| *C < 1) (hC : 0 ≤ C) (htime : time ∈ Icc (0 : ℝ) 1) :
    |time*d| *C < 1 := by
  rw [abs_mul,abs_of_nonneg htime.1]
  have hle : time*|d| ≤ |d| := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right htime.2 (abs_nonneg d)
  exact (mul_le_mul_of_nonneg_right hle hC).trans_lt hsmall

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.scalarFiberShift_bijective
#print axioms TwoAxisHelicoid.scalarFiberShift_preserves_strip
