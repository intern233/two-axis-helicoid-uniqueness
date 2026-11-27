import TwoAxisHelicoid.AnalyticPlaneLaplacian
import TwoAxisHelicoid.HarmonicComplexCoefficient
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace TwoAxisHelicoid
open Complex Filter InnerProductSpace Laplacian
open scoped Topology ContDiff

theorem planePartial_harmonic {f : ℂ → ℝ} {z : ℂ} (hf : HarmonicAt f z) (v : ℂ) :
    HarmonicAt (planePartial v f) z := by
  have he : planePartial v f = fun w => (v*scalarComplexCoefficient f w).re := by
    funext w
    exact (congrArg (fun D : ℂ →L[ℝ] ℝ => D v) (realCoefficientDerivative_reconstruct (fderiv ℝ f w))).symm
  rw [he]
  exact ((analyticAt_const (v := v)).mul (scalarComplexCoefficient_analyticAt hf)).harmonicAt.comp_CLM reCLM

theorem harmonic_coordinate_laplacian_zero {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hh : ∀ j, HarmonicAt (fun w => X w j) z) : (Δ X) z = 0 := by
  have ha : AnalyticAt ℝ X z := analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (hh j))
  ext j
  exact (ha.contDiffAt.of_le (show (2 : ℕ∞ω) ≤ ω by simp)).laplacian_CLM_comp_left
    (l := (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ)) |>.symm.trans (hh j).2.self_of_nhds

theorem harmonic_tangent_laplacian_zero {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hh : ∀ j, HarmonicAt (fun w => X w j) z) (v : ℂ) : (Δ (planePartial v X)) z = 0 := by
  have ha : AnalyticAt ℝ X z := analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (hh j))
  apply harmonic_coordinate_laplacian_zero
  intro j
  apply (harmonicAt_congr_nhds (f₂ := planePartial v (fun u => X u j)) ?_).mpr (planePartial_harmonic (hh j) v)
  filter_upwards [ha.eventually_analyticAt] with w hw
  have h := (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp w hw.differentiableAt.hasFDerivAt
  exact (congrArg (fun D : ℂ →L[ℝ] ℝ => D v) h.fderiv).symm

theorem planePartial_commute {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {X : ℂ → E} {z : ℂ} (hf : AnalyticAt ℝ X z) (u v : ℂ) :
    planePartial u (planePartial v X) z = planePartial v (planePartial u X) z := by
  have he (a b : ℂ) : planePartial a (planePartial b X) z = fderiv ℝ (fderiv ℝ X) z a b := by
    have hd := (ContinuousLinearMap.apply ℝ E b).hasFDerivAt.comp z hf.fderiv.differentiableAt.hasFDerivAt
    change fderiv ℝ ((ContinuousLinearMap.apply ℝ E b) ∘ fderiv ℝ X) z a = _
    rw [hd.fderiv]
    rfl
  rw [he,he]
  exact hf.contDiffAt.isSymmSndFDerivAt_of_omega u v

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_tangent_laplacian_zero
