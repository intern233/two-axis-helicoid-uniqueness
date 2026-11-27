import TwoAxisHelicoid.BoundedSmoothODE
import TwoAxisHelicoid.ConformalGeodesicEnergy
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

namespace TwoAxisHelicoid
open Set Metric Complex Real
open scoped Topology
set_option maxHeartbeats 1000000

def unitVelocityBump : ContDiffBump (0 : ℂ) :=
  ⟨1,2,by norm_num,by norm_num⟩

noncomputable def cutOffConformalGeodesicField (Γ : ℂ → ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (unitVelocityBump p.2 • p.2,-(unitVelocityBump p.2 : ℂ)*Γ p.1*p.2^2)

theorem cutOffConformalGeodesicField_contDiff {Γ : ℂ → ℂ} (hΓ : ContDiff ℝ 1 Γ) :
    ContDiff ℝ 1 (cutOffConformalGeodesicField Γ) := by
  have hb : ContDiff ℝ 1 (fun p : ℂ × ℂ => unitVelocityBump p.2) :=
    unitVelocityBump.contDiff.comp contDiff_snd
  have hg : ContDiff ℝ 1 (fun p : ℂ × ℂ => Γ p.1) := hΓ.comp contDiff_fst
  exact (hb.smul contDiff_snd).prodMk
    (((Complex.ofRealCLM.contDiff.comp hb).neg.mul hg).mul (contDiff_snd.pow 2))

theorem cutOffConformalGeodesicField_bound {Γ : ℂ → ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hΓ : ∀ z, ‖Γ z‖ ≤ L) (p : ℂ × ℂ) : ‖cutOffConformalGeodesicField Γ p‖ ≤ 4*L+2 := by
  by_cases hv : 2 ≤ ‖p.2‖
  · have hb : unitVelocityBump p.2 = 0 :=
      unitVelocityBump.zero_of_le_dist (by simpa [unitVelocityBump,dist_zero_right] using hv)
    simp only [cutOffConformalGeodesicField,hb,zero_smul,Complex.ofReal_zero,neg_zero,zero_mul,
      Prod.mk_zero_zero,norm_zero]
    positivity
  · have hv2 : ‖p.2‖ ≤ 2 := (lt_of_not_ge hv).le
    have hχ0 : 0 ≤ unitVelocityBump p.2 := unitVelocityBump.nonneg
    have hχ1 : unitVelocityBump p.2 ≤ 1 := unitVelocityBump.le_one
    have hfirst : ‖unitVelocityBump p.2 • p.2‖ ≤ 2 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hχ0]
      nlinarith [norm_nonneg p.2]
    have hsecond : ‖-(unitVelocityBump p.2 : ℂ)*Γ p.1*p.2^2‖ ≤ 4*L := by
      rw [norm_mul,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hχ0,norm_pow]
      calc
        unitVelocityBump p.2 * ‖Γ p.1‖ * ‖p.2‖^2 ≤ 1*L*2^2 := by gcongr; exact hΓ p.1
        _ = _ := by ring
    change max ‖unitVelocityBump p.2 • p.2‖ ‖-(unitVelocityBump p.2 : ℂ)*Γ p.1*p.2^2‖ ≤ 4*L+2
    exact max_le (hfirst.trans (by linarith)) (hsecond.trans (by linarith))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.cutOffConformalGeodesicField_bound
