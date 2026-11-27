import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.RemovableSingularity

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- The two real columns of the derivative give the scalar Cauchy--Riemann
condition for a real differentiable map of planes. -/
theorem complex_differentiable_iff_columns {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℂ f z ↔ fderiv ℝ f z I = I * fderiv ℝ f z 1 := by
  constructor
  · intro h
    rw [h.fderiv_restrictScalars ℝ]
    change (fderiv ℂ f z) I = I * (fderiv ℂ f z) 1
    simp
  · intro h
    let d := fderiv ℝ f z
    let c : ℂ →L[ℂ] ℂ := (ContinuousLinearMap.id ℂ ℂ).smulRight (d 1)
    apply (hasFDerivAt_of_restrictScalars ℝ hf.hasFDerivAt (f' := c) ?_).differentiableAt
    ext w
    change w * d 1 = d w
    have he : w.re • (1 : ℂ) + w.im • I = w := by
      apply Complex.ext <;> simp [Complex.real_smul]
    calc
      w * d 1 = (w.re • (1:ℂ) + w.im • I) * d 1 := congrArg (· * d 1) he.symm
      _ = w.re • d 1 + w.im • d I := by
        rw [show d I = I * d 1 from h,add_mul,smul_mul_assoc,smul_mul_assoc,one_mul]
      _ = d (w.re • (1:ℂ) + w.im • I) := by rw [map_add,map_smul,map_smul]
      _ = d w := congrArg d he

/-- A real analytic plane map complex analytic on one patch is complex
analytic on the entire connected open parameter domain. -/
theorem analytic_complex_of_open_patch {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℝ f U) {b : ℂ} (hb : b ∈ U)
    (hpatch : AnalyticAt ℂ f b) : AnalyticOnNhd ℂ f U := by
  let D := fun z => fderiv ℝ f z I - I * fderiv ℝ f z 1
  have hD : AnalyticOnNhd ℝ D U := by
    intro z hz
    have hd (u : ℂ) : AnalyticAt ℝ (fun w => fderiv ℝ f w u) z :=
      ((ContinuousLinearMap.apply ℝ ℂ u).analyticAt _).comp (hf z hz).fderiv
    exact (hd I).sub (analyticAt_const.mul (hd 1))
  have hnear : D =ᶠ[𝓝 b] 0 := by
    filter_upwards [(isOpen_analyticAt ℂ f).mem_nhds hpatch,hU.mem_nhds hb] with w hw hwU
    exact sub_eq_zero.mpr ((complex_differentiable_iff_columns (hf w hwU).differentiableAt).mp hw.differentiableAt)
  have hall := hD.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hb hnear
  apply DifferentiableOn.analyticOnNhd _ hU
  exact fun z hz => ((complex_differentiable_iff_columns (hf z hz).differentiableAt).mpr
    (sub_eq_zero.mp (hall hz))).differentiableWithinAt

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.analytic_complex_of_open_patch
