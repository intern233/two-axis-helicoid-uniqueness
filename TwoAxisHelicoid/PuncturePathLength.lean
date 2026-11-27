import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology

theorem weighted_path_length_lower_bound {γ v : ℝ → ℂ} {ρ : ℝ → ℝ} {b s C : ℝ}
    (hbs : b ≤ s) (hC : 0 ≤ C)
    (hd : ∀ u ∈ Icc b s, HasDerivAt γ (v u) u)
    (hv : ContinuousOn v (Icc b s)) (hρ : ContinuousOn ρ (Icc b s))
    (hn : ∀ u ∈ Icc b s, γ u ≠ 0)
    (hlower : ∀ u ∈ Icc b s, C/‖γ u‖^2 ≤ ρ u) :
    C*‖(γ s)⁻¹-(γ b)⁻¹‖ ≤ ∫ u : ℝ in b..s, ρ u*‖v u‖ := by
  have hγ : ContinuousOn γ (Icc b s) := fun u hu => (hd u hu).continuousAt.continuousWithinAt
  let d : ℝ → ℂ := fun u => -(v u)/(γ u)^2
  have hdi (u : ℝ) (hu : u ∈ Icc b s) : HasDerivAt (fun x => (γ x)⁻¹) (d u) u :=
    (hd u hu).inv (hn u hu)
  have hdc : ContinuousOn d (Icc b s) := hv.neg.div (hγ.pow 2) (fun u hu => pow_ne_zero 2 (hn u hu))
  have hI : IntervalIntegrable d volume b s := hdc.intervalIntegrable_of_Icc hbs
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hdi u (by simpa only [uIcc_of_le hbs] using hu)) hI
  have hnI := intervalIntegral.norm_integral_le_integral_norm (f := d) (μ := volume) hbs
  rw [hFTC] at hnI
  have hbound : (∫ u : ℝ in b..s, C*‖d u‖) ≤ ∫ u : ℝ in b..s, ρ u*‖v u‖ := by
    apply intervalIntegral.integral_mono_on hbs
      ((continuousOn_const.mul hdc.norm).intervalIntegrable_of_Icc hbs)
      ((hρ.mul hv.norm).intervalIntegrable_of_Icc hbs)
    intro u hu
    have h := mul_le_mul_of_nonneg_right (hlower u hu) (norm_nonneg (v u))
    change C*‖d u‖ ≤ ρ u*‖v u‖
    have he : C*‖d u‖ = C/‖γ u‖^2*‖v u‖ := by
      simp only [d,norm_div,norm_neg,norm_pow]
      ring
    rw [he]
    exact h
  rw [intervalIntegral.integral_const_mul] at hbound
  exact (mul_le_mul_of_nonneg_left hnI hC).trans hbound

/-- A positive inverse-square lower bound forces infinite weighted length along
every C1 path tending to the puncture. The velocity is explicitly supplied. -/
theorem weighted_path_length_tendsto_top {γ v : ℝ → ℂ} {ρ : ℝ → ℝ} {b C : ℝ}
    (hb : b < 1) (hC : 0 < C)
    (hd : ∀ u ∈ Ico b 1, HasDerivAt γ (v u) u)
    (hv : ContinuousOn v (Ico b 1)) (hρ : ContinuousOn ρ (Ico b 1))
    (hn : ∀ u ∈ Ico b 1, γ u ≠ 0)
    (hlower : ∀ u ∈ Ico b 1, C/‖γ u‖^2 ≤ ρ u)
    (hlim : Tendsto γ (𝓝[<] 1) (𝓝[≠] (0:ℂ))) :
    Tendsto (fun s => ∫ u : ℝ in b..s, ρ u*‖v u‖) (𝓝[<] 1) atTop := by
  have hinv := tendsto_inv₀_nhdsNE_zero.comp hlim
  have hnorm : Tendsto (fun s => ‖(γ s)⁻¹‖) (𝓝[<] (1:ℝ)) atTop :=
    tendsto_norm_cobounded_atTop.comp hinv
  have hsub : Tendsto (fun s => ‖(γ s)⁻¹‖-‖(γ b)⁻¹‖) (𝓝[<] (1:ℝ)) atTop :=
    Filter.tendsto_atTop.mpr (fun R => by
      filter_upwards [hnorm.eventually_ge_atTop (R+‖(γ b)⁻¹‖)] with s hs
      linarith)
  have hdist : Tendsto (fun s => ‖(γ s)⁻¹-(γ b)⁻¹‖) (𝓝[<] (1:ℝ)) atTop :=
    tendsto_atTop_mono (fun s => norm_sub_norm_le _ _) hsub
  refine tendsto_atTop_mono' _ ?_ (hdist.const_mul_atTop hC)
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hb),self_mem_nhdsWithin] with s hsb hs1
  have hsubI : Icc b s ⊆ Ico b 1 := fun u hu => ⟨hu.1,hu.2.trans_lt hs1⟩
  exact weighted_path_length_lower_bound hsb.le hC.le
    (fun u hu => hd u (hsubI hu)) (hv.mono hsubI) (hρ.mono hsubI)
    (fun u hu => hn u (hsubI hu)) (fun u hu => hlower u (hsubI hu))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.weighted_path_length_tendsto_top
