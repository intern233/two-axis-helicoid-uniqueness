import TwoAxisHelicoid.PolynomialHeightDerivative
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Meromorphic.Basic

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology

/-- Uniform polynomial control of a holomorphic function's real part on
a punctured disk excludes an essential singularity, even when its
imaginary part has no prescribed bound. -/
theorem meromorphic_of_polynomial_real_height {H : ℂ → ℂ} {R C : ℝ} (hR : 0<R) (hC : 0<C) (N : ℕ)
    (diff : ∀ z : ℂ, 0<‖z‖ → ‖z‖<R → DifferentiableAt ℂ H z)
    (bound : ∀ z : ℂ, 0<‖z‖ → ‖z‖<R → |(H z).re|≤C/‖z‖^N) : MeromorphicAt H 0 := by
  let ρ := min 1 (R/4)
  have hr : 0<ρ := lt_min zero_lt_one (by positivity)
  have hhalf : ρ<R/2 := (min_le_right 1 (R/4)).trans_lt (by linarith)
  have inside : ρ<R := hhalf.trans (by linarith)
  obtain ⟨B,bd⟩ := (isCompact_sphere (0:ℂ) ρ).exists_bound_of_continuousOn
    (f := H) (fun z hz => by
      have n : ‖z‖=ρ := by simpa only [mem_sphere,dist_zero_right] using hz
      exact (diff z (n ▸ hr) (n ▸ inside)).continuousAt.continuousWithinAt)
  let D : ℝ := 16*2^N*C
  have dpos : 0≤D := by dsimp [D]; positivity
  have radial (z : ℂ) (nz : 0<‖z‖) (small : ‖z‖<ρ) :
      ‖z‖^(N+1)*‖H z‖≤|B|+D*ρ := by
    let r := ‖z‖
    let u : ℂ := r⁻¹ • z
    have unit : ‖u‖=1 := by
      rw [show u=r⁻¹ • z from rfl,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr nz)]
      exact inv_mul_cancel₀ nz.ne'
    have n (x : ℝ) (hx : 0≤x) : ‖x • u‖=x := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hx,unit,mul_one]
    let F := fun x : ℝ => H (x • u)
    have drv (x : ℝ) (hx : x∈Icc r ρ) : HasDerivAt F (u*deriv H (x • u)) x := by
      have pos := nz.trans_le hx.1
      have hd := diff (x • u) (by rw [n _ pos.le]; exact pos) (by rw [n _ pos.le]; exact hx.2.trans_lt inside)
      have axis : HasDerivAt (fun t : ℝ => t • u) u x := by simpa only [id_eq,one_smul] using! (hasDerivAt_id x).smul_const u
      exact (hd.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt x axis
    have grad (x : ℝ) (hx : x∈Icc r ρ) : ‖u*deriv H (x • u)‖≤D/r^(N+1) := by
      have pos := nz.trans_le hx.1
      have h := polynomial_real_height_derivative_bound hC N diff bound
        (z := x • u) (by rw [n _ pos.le]; exact pos) (by rw [n _ pos.le]; exact hx.2.trans_lt hhalf)
      rw [norm_mul,unit,one_mul]
      rw [n _ pos.le] at h
      exact h.trans (div_le_div_of_nonneg_left dpos (pow_pos nz _) (pow_le_pow_left₀ nz.le hx.1 _))
    have var := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ)
      (fun x hx => (drv x hx).hasDerivWithinAt) grad (convex_Icc r ρ)
      (right_mem_Icc.mpr small.le) (left_mem_Icc.mpr small.le)
    have ru : r • u=z := by rw [show u=r⁻¹ • z from rfl,smul_smul,mul_inv_cancel₀ nz.ne',one_smul]
    have bs : ‖H (ρ • u)‖≤B := bd _ (by rw [mem_sphere,dist_zero_right,n _ hr.le])
    have v : ‖H z-H (ρ • u)‖≤D/r^(N+1)*ρ := by
      change ‖H (r • u)-H (ρ • u)‖≤_*‖r-ρ‖ at var
      rw [ru,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr small.le)] at var
      exact var.trans (mul_le_mul_of_nonneg_left (by linarith : -(r-ρ)≤ρ) (div_nonneg dpos (pow_nonneg nz.le _)))
    have hh : ‖H z‖≤ |B|+D/r^(N+1)*ρ := by
      have tr := norm_sub_norm_le (H z) (H (ρ • u))
      linarith [le_abs_self B]
    have rp : r^(N+1)≤1 := pow_le_one₀ nz.le (small.le.trans (min_le_left _ _))
    calc
      ‖z‖^(N+1)*‖H z‖ ≤ r^(N+1)*(|B|+D/r^(N+1)*ρ) := mul_le_mul_of_nonneg_left hh (pow_nonneg nz.le _)
      _ = r^(N+1)*|B|+D*ρ := by
        have nr : r^(N+1)≠0 := pow_ne_zero _ nz.ne'
        calc
          _ = r^(N+1)*|B|+(r^(N+1)*(D/r^(N+1)))*ρ := by ring
          _ = _ := by rw [mul_div_cancel₀ D nr]
      _ ≤ _ := add_le_add_left ((mul_le_mul_of_nonneg_right rp (abs_nonneg B)).trans_eq (one_mul _)) _
  let G := fun z : ℂ => (z-(0:ℂ))^(N+2) • H z
  refine ⟨N+2,Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_⟩
  · filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) hR)] with z hz hs
    have pos : 0<‖z‖ := norm_pos_iff.mpr hz
    exact ((differentiableAt_id.sub_const 0).pow _).smul (diff z pos (by simpa only [mem_ball,dist_zero_right] using hs))
  · change ContinuousAt G 0
    rw [continuousAt_iff_punctured_nhds,show G 0=0 by simp [G],tendsto_zero_iff_norm_tendsto_zero]
    have zlim : Tendsto (fun z : ℂ => ‖z‖*(|B|+D*ρ)) (𝓝[≠] 0) (𝓝 0) := by
      simpa only [norm_zero,zero_mul] using (continuous_norm.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ)≤𝓝 0)).mul_const (|B|+D*ρ)
    apply squeeze_zero' (.of_forall fun z => norm_nonneg (G z)) _ zlim
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) hr)] with z hz hs
    have b := radial z (norm_pos_iff.mpr hz) (by simpa only [mem_ball,dist_zero_right] using hs)
    change ‖(z-0)^(N+2) • H z‖≤_
    rw [sub_zero,norm_smul,norm_pow,show N+2=(N+1)+1 by omega,pow_succ]
    exact (le_of_eq (by ring : ‖z‖^(N+1)*‖z‖*‖H z‖=‖z‖*(‖z‖^(N+1)*‖H z‖))).trans
      (mul_le_mul_of_nonneg_left b (norm_nonneg _))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.meromorphic_of_polynomial_real_height
