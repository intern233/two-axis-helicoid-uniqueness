import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology

/-- A continuous real function with positive derivative at its initial zero and
no subsequent zero stays positive throughout the interval. -/
theorem positive_on_interval_of_simple_zero {f : ℝ → ℝ} {b d : ℝ}
    (hf : ContinuousOn f (Ioo 0 b)) (h0 : f 0 = 0) (hd : HasDerivAt f d 0) (hdpos : 0 < d)
    (hn : ∀ x ∈ Ioo 0 b, f x ≠ 0) {x : ℝ} (hx : x ∈ Ioo 0 b) : 0 < f x := by
  have hs : ∀ᶠ y in 𝓝[>] (0:ℝ), 0 < y⁻¹*f y := by
    simpa only [zero_add,h0,sub_zero,smul_eq_mul] using
      hd.tendsto_slope_zero_right.eventually (Ioi_mem_nhds hdpos)
  have hlt : ∀ᶠ y in 𝓝[>] (0:ℝ), y < x :=
    (eventually_lt_nhds hx.1).filter_mono nhdsWithin_le_nhds
  have hex : ∀ᶠ y in 𝓝[>] (0:ℝ), 0 < y ∧ y < x ∧ 0 < f y := by
    filter_upwards [self_mem_nhdsWithin,hlt,hs] with y hy hxy hprod
    exact ⟨hy,hxy,(mul_pos_iff_of_pos_left (inv_pos.mpr hy)).mp hprod⟩
  obtain ⟨y,hy,hyx,hyf⟩ := hex.exists
  by_contra hnot
  have hfx : f x ≤ 0 := le_of_not_gt hnot
  have hc : ContinuousOn f (Icc y x) := hf.mono (by
    intro z hz
    exact ⟨hy.trans_le hz.1,hz.2.trans_lt hx.2⟩)
  obtain ⟨z,hz,hzero⟩ := intermediate_value_Icc' hyx.le hc ⟨hfx,hyf.le⟩
  exact hn z ⟨hy.trans_le hz.1,hz.2.trans_lt hx.2⟩ hzero

end TwoAxisHelicoid
