import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Complex Metric

noncomputable def analyticTaylorTerm (f : ℂ → ℂ) (c z : ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ * iteratedDeriv n f c * (z-c)^n

noncomputable def analyticTaylor (f : ℂ → ℂ) (c : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, analyticTaylorTerm f c z n

theorem analyticTaylorTerm_norm_le {f : ℂ → ℂ} {c z : ℂ} {R r M : ℝ}
    (hR : 0 < R) (_hr : 0 ≤ r) (hf : DiffContOnCl ℂ f (ball c R))
    (hM : ∀ w ∈ sphere c R, ‖f w‖ ≤ M) (hz : ‖z-c‖ ≤ r) (n : ℕ) :
    ‖analyticTaylorTerm f c z n‖ ≤ M*(r/R)^n := by
  have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hf hM
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  unfold analyticTaylorTerm
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast, norm_pow]
  calc
    _ ≤ (n.factorial : ℝ)⁻¹*((n.factorial : ℝ)*M/R^n)*r^n := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hfac.le)
      · exact pow_le_pow_left₀ (norm_nonneg _) hz n
      · positivity
      · have hm0 : 0 ≤ (n.factorial : ℝ)*M/R^n := (norm_nonneg _).trans hd
        positivity
    _ = _ := by
      rw [div_pow]
      field_simp

/-- Uniform geometric Taylor remainder, proved from the actual holomorphic function. -/
theorem analyticTaylor_remainder_bound {f : ℂ → ℂ} {c z : ℂ} {R r M : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R) (_hM0 : 0 ≤ M)
    (hf : DiffContOnCl ℂ f (ball c R))
    (hM : ∀ w ∈ sphere c R, ‖f w‖ ≤ M) (hz : ‖z-c‖ ≤ r) (N : ℕ) :
    ‖f z-analyticTaylor f c N z‖ ≤ M*(r/R)^N/(1-r/R) := by
  have hratio0 : 0 ≤ r/R := div_nonneg hr hR.le
  have hratio1 : r/R < 1 := (div_lt_one hR).mpr hrR
  have hzball : z ∈ ball c R := mem_ball_iff_norm.mpr (hz.trans_lt hrR)
  have hs : HasSum (analyticTaylorTerm f c z) (f z) := by
    convert Complex.hasSum_taylorSeries_on_ball hf.differentiableOn hzball using 1
    funext n
    simp only [analyticTaylorTerm, smul_eq_mul]
    ring
  have hg := (hasSum_geometric_of_lt_one hratio0 hratio1).mul_left (M*(r/R)^N)
  have hb : ∀ k : ℕ, ‖analyticTaylorTerm f c z (k+N)‖ ≤ M*(r/R)^N*(r/R)^k := by
    intro k
    calc
      _ ≤ M*(r/R)^(k+N) := analyticTaylorTerm_norm_le hR hr hf hM hz (k+N)
      _ = _ := by rw [pow_add]; ring
  have hnorm := Summable.of_nonneg_of_le (fun k => norm_nonneg _) hb hg.summable
  have hsplit := hs.summable.sum_add_tsum_nat_add N
  have heq : f z-analyticTaylor f c N z = ∑' k : ℕ, analyticTaylorTerm f c z (k+N) := by
    unfold analyticTaylor
    rw [← hs.tsum_eq]
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hsplit.symm)
  rw [heq]
  calc
    _ ≤ ∑' k : ℕ, ‖analyticTaylorTerm f c z (k+N)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℕ, M*(r/R)^N*(r/R)^k := hnorm.tsum_le_tsum hb hg.summable
    _ = _ := by rw [hg.tsum_eq]; rfl

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.analyticTaylor_remainder_bound
