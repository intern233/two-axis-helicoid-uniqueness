import TwoAxisHelicoid.ConformalGeodesicEnergy
import TwoAxisHelicoid.WeierstrassLogGauss
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace TwoAxisHelicoid
open Complex Real
open scoped ContDiff
set_option maxHeartbeats 1000000

noncomputable def logCoshMetric (W : ℂ → ℂ) (z : ℂ) : ℝ :=
  Real.log (Real.cosh (W z).re)

noncomputable def logGaussConnection (W : ℂ → ℂ) (z : ℂ) : ℂ :=
  (Real.tanh (W z).re : ℂ)*deriv W z

theorem logCoshMetric_nonneg (W : ℂ → ℂ) (z : ℂ) : 0 ≤ logCoshMetric W z :=
  Real.log_nonneg (Real.one_le_cosh _)

theorem logCoshMetric_energy (W : ℂ → ℂ) (z v : ℂ) :
    conformalKineticEnergy (logCoshMetric W) z v =
      (Real.cosh (W z).re)^2*Complex.normSq v := by
  simp only [conformalKineticEnergy,logCoshMetric,two_mul,Real.exp_add,
    Real.exp_log (Real.cosh_pos _)]
  ring

/-- The connection coefficient is computed from the actual conformal
factor of the height-normalized Weierstrass immersion. -/
theorem logCoshMetric_connection {W : ℂ → ℂ} {D z : ℂ} (hW : HasDerivAt W D z) :
    DifferentiableAt ℝ (logCoshMetric W) z ∧
      ∀ w : ℂ, fderiv ℝ (logCoshMetric W) z w = (logGaussConnection W z*w).re := by
  have hr := Complex.reCLM.hasFDerivAt.comp z (hW.hasFDerivAt.restrictScalars ℝ)
  have hd := hr.cosh.log (Real.cosh_pos (W z).re).ne'
  refine ⟨hd.differentiableAt,?_⟩
  intro w
  change fderiv ℝ (fun x => Real.log (Real.cosh ((Complex.reCLM ∘ W) x))) z w = _
  rw [hd.fderiv]
  change (Real.cosh (W z).re)⁻¹*(Real.sinh (W z).re*(w*D).re) = _
  simp only [logGaussConnection,hW.deriv,Real.tanh_eq_sinh_div_cosh,Complex.mul_re,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem logGaussConnection_contDiffAt {W : ℂ → ℂ} {z : ℂ} (hW : AnalyticAt ℂ W z) :
    ContDiffAt ℝ (∞ : WithTop ℕ∞) (logGaussConnection W) z := by
  have hr : ContDiffAt ℝ (∞ : WithTop ℕ∞) (fun w => (W w).re) z :=
    Complex.reCLM.contDiff.contDiffAt.comp z (hW.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hd : ContDiffAt ℝ (∞ : WithTop ℕ∞) (deriv W) z :=
    (hW.deriv.restrictScalars (𝕜 := ℝ)).contDiffAt
  have ht : ContDiffAt ℝ (∞ : WithTop ℕ∞) (fun w => Real.tanh (W w).re) z := by
    simpa only [Real.tanh_eq_sinh_div_cosh,Pi.div_apply] using!
      hr.sinh.div hr.cosh (Real.cosh_pos _).ne'
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z ht).mul hd

theorem logGaussConnection_norm_le (W : ℂ → ℂ) (z : ℂ) :
    ‖logGaussConnection W z‖ ≤ ‖deriv W z‖ := by
  rw [logGaussConnection,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_tanh_lt_one _).le

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.logCoshMetric_connection
