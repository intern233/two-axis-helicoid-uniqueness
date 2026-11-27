import TwoAxisHelicoid.PhysicalRawDifferentialEnd
import Mathlib.Analysis.Complex.OpenMapping

namespace TwoAxisHelicoid
open Complex Set Filter Topology Metric Bornology
open scoped Topology

/-- A holomorphic reciprocal inverse which covers every sufficiently large
height forces the height to escape along the entire puncture. -/
theorem punctured_height_tends_to_infinity_of_inverse {H k : ℂ → ℂ} (hk : AnalyticAt ℂ k 0)
    (k0 : k 0=0) (limit : Tendsto (fun ξ : ℂ => k ξ⁻¹) (cobounded ℂ) (𝓝[≠] 0))
    (right : ∀ᶠ ξ : ℂ in cobounded ℂ, H (k ξ⁻¹)=ξ) : Tendsto H (𝓝[≠] 0) (cobounded ℂ) := by
  have inv : Tendsto (Inv.inv : ℂ → ℂ) (𝓝[≠] 0) (cobounded ℂ) := tendsto_inv₀_nhdsNE_zero
  have punctured : ∀ᶠ z in 𝓝[≠] (0:ℂ), k z≠0 := by
    simpa only [inv_inv,mem_compl_iff,mem_singleton_iff] using inv.eventually (limit.eventually self_mem_nhdsWithin)
  have op : 𝓝 (0:ℂ)≤map k (𝓝 0) := by
    have nc : ¬∀ᶠ z in 𝓝 (0:ℂ), k z=k 0 := by
      intro constant
      obtain ⟨z,ne,zero⟩ := (punctured.and (constant.filter_mono nhdsWithin_le_nhds)).exists
      exact ne (zero.trans k0)
    simpa only [k0] using hk.eventually_constant_or_nhds_le_map_nhds.resolve_left nc
  have eq : ∀ᶠ z in 𝓝[≠] (0:ℂ), H (k z)=z⁻¹ := by simpa only [inv_inv] using inv.eventually right
  intro V hV
  have onPuncture : ∀ᶠ z in 𝓝[≠] (0:ℂ), H (k z)∈V := by
    filter_upwards [eq,inv.eventually hV] with z he hv
    rwa [he]
  have pre : ∀ᶠ z in 𝓝 (0:ℂ), k z≠0 → H (k z)∈V := by
    have h : ∀ᶠ z in 𝓝 (0:ℂ), z≠0 → H (k z)∈V := by
      simpa only [eventually_nhdsWithin_iff,mem_compl_iff,mem_singleton_iff] using onPuncture
    filter_upwards [h] with z hz nz
    exact hz (fun zero => nz (zero ▸ k0))
  have extended : ∀ᶠ z in 𝓝 (0:ℂ), z≠0 → H z∈V := op (show {z : ℂ | z≠0 → H z∈V}∈map k (𝓝 0) from pre)
  exact eventually_nhdsWithin_iff.mpr extended

/-- Restrict the genuine reciprocal inverse to an exterior round disk.
The source contains a whole punctured neighborhood and can be required
to lie inside any specified punctured neighborhood. -/
theorem punctured_height_exterior_chart {H k : ℂ → ℂ} (hk : AnalyticAt ℂ k 0) (k0 : k 0=0)
    (limit : Tendsto (fun ξ : ℂ => k ξ⁻¹) (cobounded ℂ) (𝓝[≠] 0))
    (left : ∀ᶠ z in 𝓝[≠] (0:ℂ), AnalyticAt ℂ H z ∧ k (H z)⁻¹=z)
    (right : ∀ᶠ ξ : ℂ in cobounded ℂ, H (k ξ⁻¹)=ξ)
    {U V : Set ℂ} (small : U∈𝓝[≠] (0:ℂ)) (large : V∈cobounded ℂ) :
    ∃ (d : OpenPartialHomeomorph ℂ ℂ) (R : ℝ), 0<R ∧ d.target={ξ | R<‖ξ‖} ∧
      d.source∈𝓝[≠] (0:ℂ) ∧ d.source⊆U ∧ d.target⊆V ∧
      (∀ z, d z=H z) ∧ (∀ ξ, d.symm ξ=k ξ⁻¹) ∧
      (∀ z∈d.source, AnalyticAt ℂ d z) ∧ (∀ ξ∈d.target, AnalyticAt ℂ d.symm ξ) := by
  have tend := punctured_height_tends_to_infinity_of_inverse hk k0 limit right
  obtain ⟨r,rp,within⟩ := Metric.mem_nhdsWithin_iff.mp (left.and small)
  let W := ball (0:ℂ) r \ {0}
  have Wopen : IsOpen W := isOpen_ball.sdiff isClosed_singleton
  have Wmem : W∈𝓝[≠] (0:ℂ) := inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ rp)) self_mem_nhdsWithin
  let K := fun ξ : ℂ => k ξ⁻¹
  have an : ∀ᶠ ξ : ℂ in cobounded ℂ, AnalyticAt ℂ K ξ := by
    have ne : ∀ᶠ ξ : ℂ in cobounded ℂ, ξ≠0 := by
      filter_upwards [eventually_cobounded_le_norm (E := ℂ) 1] with ξ h zero
      rw [zero,norm_zero] at h
      exact (not_le_of_gt zero_lt_one) h
    filter_upwards [tendsto_inv₀_cobounded.eventually hk.eventually_analyticAt,ne] with ξ hw hn
    exact hw.comp (analyticAt_id.inv hn)
  have largeV : ∀ᶠ ξ : ℂ in cobounded ℂ, ξ∈V := large
  obtain ⟨b,_,good⟩ := hasBasis_cobounded_norm.mem_iff.mp (((limit.eventually Wmem).and right).and (largeV.and an))
  let R := max 1 b
  let T := {ξ : ℂ | R<‖ξ‖}
  have gp {ξ : ℂ} (h : ξ∈T) := good (show b≤‖ξ‖ from (le_max_right 1 b).trans (le_of_lt h))
  have hp {z : ℂ} (h : z∈W) := within h
  let d : OpenPartialHomeomorph ℂ ℂ := {
    toFun := H
    invFun := K
    source := W ∩ H ⁻¹' T
    target := T
    map_source' := fun _ hz => hz.2
    map_target' := fun ξ hz => ⟨(gp hz).1.1,by change H (k ξ⁻¹)∈T; rwa [(gp hz).1.2]⟩
    left_inv' := fun _ hz => (hp hz.1).1.2
    right_inv' := fun _ hz => (gp hz).1.2
    open_source := ContinuousOn.isOpen_inter_preimage (fun _ h => (hp h).1.1.continuousAt.continuousWithinAt)
      Wopen (isOpen_lt continuous_const continuous_norm)
    open_target := isOpen_lt continuous_const continuous_norm
    continuousOn_toFun := fun _ h => (hp h.1).1.1.continuousAt.continuousWithinAt
    continuousOn_invFun := fun _ h => (gp h).2.2.continuousAt.continuousWithinAt }
  have far : T∈cobounded ℂ := by
    filter_upwards [eventually_cobounded_le_norm (E := ℂ) (R+1)] with ξ h
    change R<‖ξ‖
    linarith
  exact ⟨d,R,lt_of_lt_of_le zero_lt_one (le_max_left _ _),rfl,inter_mem Wmem (tend far),
    fun _ h => (hp h.1).2,fun _ h => (gp h).2.1,fun _ => rfl,fun _ => rfl,
    fun _ h => (hp h.1).1.1,fun _ h => (gp h).2.2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.punctured_height_exterior_chart
