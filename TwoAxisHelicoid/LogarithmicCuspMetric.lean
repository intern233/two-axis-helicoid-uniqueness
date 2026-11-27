import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.HaarToSphere

namespace TwoAxisHelicoid
open Real Complex Set Filter MeasureTheory Metric
open scoped Topology

/-- The finite-area conformal density outside the circle of radius two. -/
noncomputable def exteriorCuspDensity (r : ℝ) : ℝ := if 2<r then (r*Real.log r)⁻¹ else 0

theorem exteriorCuspDensity_nonneg (r : ℝ) : 0≤exteriorCuspDensity r := by
  unfold exteriorCuspDensity
  split_ifs with h
  · exact inv_nonneg.mpr (mul_nonneg (by linarith) (Real.log_nonneg (by linarith)))
  · exact le_rfl

/-- The squared density is integrable in planar Lebesgue measure.
After polar integration the radial integral is that of 1/(r log² r). -/
theorem exterior_cusp_finite_area :
    Integrable (fun z : ℂ => exteriorCuspDensity ‖z‖^2) volume := by
  have eq : (fun r : ℝ => r*exteriorCuspDensity r^2) =
      (Ioi (2:ℝ)).indicator (fun r => r⁻¹/(Real.log r)^2) := by
    funext r
    by_cases h : 2<r
    · rw [indicator_of_mem (show r∈Ioi (2:ℝ) from h)]
      simp only [exteriorCuspDensity,ite_eq_left h]
      have nz : r≠0 := by linarith
      field_simp
    · simp [exteriorCuspDensity,h]
  apply (integrable_fun_norm_addHaar (volume : Measure ℂ) (f := fun r => exteriorCuspDensity r^2)).mpr
  simp only [Complex.finrank_real_complex,show 2-1=1 by decide,pow_one,smul_eq_mul,eq]
  exact ((integrable_indicator_iff measurableSet_Ioi).mpr (integrableOn_inv_div_log_sq_Ioi (by norm_num : (1:ℝ)<2))).integrableOn

/-- The differential of log log radius is dominated by the cusp
density in every direction. -/
theorem loglog_radius_derivative_bound {z : ℂ} (hz : 2<‖z‖) (v : ℂ) :
    let F := fun w : ℂ => Real.log (Real.log ‖w‖)
    DifferentiableAt ℝ F z ∧ |fderiv ℝ F z v|≤exteriorCuspDensity ‖z‖*‖v‖ := by
  let r := ‖z‖
  let F := fun w : ℂ => Real.log (Real.log ‖w‖)
  let N := fderiv ℝ (fun w : ℂ => ‖w‖) z
  have rp : 0<r := by dsimp [r]; linarith
  have lp : 0<Real.log r := Real.log_pos (by dsimp [r]; linarith)
  have dn : DifferentiableAt ℝ (fun w : ℂ => ‖w‖) z :=
    (differentiableAt_id (𝕜 := ℝ)).norm ℝ (norm_pos_iff.mp rp)
  have logD := (Real.hasDerivAt_log lp.ne').comp r (Real.hasDerivAt_log rp.ne')
  have d : HasDerivAt (fun s : ℝ => Real.log (Real.log s)) ((r*Real.log r)⁻¹) r := by
    simpa only [mul_inv_rev,Function.comp_def] using logD
  have h := d.comp_hasFDerivAt z dn.hasFDerivAt
  have val : fderiv ℝ F z v=(r*Real.log r)⁻¹*(N v) := congrArg (fun D : ℂ →L[ℝ] ℝ => D v) h.fderiv
  refine ⟨h.differentiableAt,?_⟩
  change |fderiv ℝ F z v|≤exteriorCuspDensity r*‖v‖
  rw [val,abs_mul,abs_of_pos (inv_pos.mpr (mul_pos rp lp)),exteriorCuspDensity,ite_eq_left hz]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (mul_nonneg rp.le lp.le))
  have bound := N.le_opNorm v
  rw [show ‖N‖=1 from norm_fderiv_norm dn,one_mul] at bound
  exact bound

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exterior_cusp_finite_area
#print axioms TwoAxisHelicoid.loglog_radius_derivative_bound
