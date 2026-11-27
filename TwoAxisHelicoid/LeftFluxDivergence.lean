import TwoAxisHelicoid.SmallVerticalBounds
import TwoAxisHelicoid.HeightFlux
import Mathlib.Topology.Algebra.Order.Field

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology
attribute [local irreducible] verticalA

/-- A simple bound sufficient for the flux degeneration argument; no horizontal
period certificate is used. -/
theorem verticalA_sub_half_lt_height {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/4) :
    0 < verticalA t-1/2 ∧ verticalA t-1/2 < t := by
  have ha := verticalA_small_bounds ht htu
  have hlog : Real.log 2 < 1 :=
    (Real.log_lt_iff_lt_exp (by norm_num)).mpr Real.exp_one_gt_two
  have hratio : t/Real.pi < t := by
    apply (div_lt_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_gt_three]
  have hm := mul_lt_of_lt_one_right (div_pos ht Real.pi_pos) hlog
  constructor <;> linarith

theorem small_height_eventually_right :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t ∧ t ≤ 1/4 := by
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hu : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1/4 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/4)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos,hu] with t ht htu
  exact ⟨ht,htu.le⟩

theorem verticalA_tendsto_half_left :
    Tendsto verticalA (𝓝[>] (0 : ℝ)) (𝓝 (1/2 : ℝ)) := by
  have hdiff : Tendsto (fun t : ℝ => verticalA t-1/2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards [small_height_eventually_right] with t ht
      exact (verticalA_sub_half_lt_height ht.1 ht.2).1.le
    · filter_upwards [small_height_eventually_right] with t ht
      exact (verticalA_sub_half_lt_height ht.1 ht.2).2.le
    · exact tendsto_id'.mpr nhdsWithin_le_nhds
  simpa only [sub_add_cancel,zero_add] using hdiff.add_const (1/2 : ℝ)

noncomputable def normalizedHeightFluxMinimum (t : ℝ) : ℝ :=
  2*Real.pi*(1-verticalA t)/t

theorem normalizedHeightFluxMinimum_lower {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/4) :
    Real.pi/(2*t) ≤ normalizedHeightFluxMinimum t := by
  have ha := (verticalA_sub_half_lt_height ht htu).2
  have hn : Real.pi/2 ≤ 2*Real.pi*(1-verticalA t) := by
    nlinarith [Real.pi_pos,mul_nonneg Real.pi_pos.le
      (show 0 ≤ 3/4-verticalA t by linarith)]
  unfold normalizedHeightFluxMinimum
  calc
    _ = (Real.pi/2)/t := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hn ht.le

theorem normalizedHeightFluxMinimum_tendsto_atTop :
    Tendsto normalizedHeightFluxMinimum (𝓝[>] (0 : ℝ)) atTop := by
  have hb : Tendsto (fun t : ℝ => Real.pi/(2*t)) (𝓝[>] (0 : ℝ)) atTop := by
    have h := Tendsto.const_mul_atTop (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 2))
      (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
    convert h using 1
    ext t
    ring
  apply tendsto_atTop_mono' (𝓝[>] (0 : ℝ)) _ hb
  filter_upwards [small_height_eventually_right] with t ht
  exact normalizedHeightFluxMinimum_lower ht.1 ht.2

/-- Every nonzero flux value for the normalized actual generator periods
exceeds any fixed bound at sufficiently small positive height. Identifying
arbitrary surface homology with these generators is a separate geometric step. -/
theorem normalized_height_basis_flux_eventually_large (B : ℝ) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ∀ (ht : 0 < t) (c v : ℝ),
      |c| = 2*(1-verticalA t) → v ∈ range (heightBasisFlux t ht c) →
      v ≠ 0 → B ≤ |v| := by
  filter_upwards [small_height_eventually_right,
    (tendsto_atTop.1 normalizedHeightFluxMinimum_tendsto_atTop B)] with t ht hB
  intro ht' c v hc hv hv0
  have ha := (verticalA_spec (small_height_mem_vertical_domain ht.1 ht.2)).1.2
  exact hB.trans ((heightBasisFlux_normalized_minimum ht' ha hc).2 v hv hv0)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.normalized_height_basis_flux_eventually_large
