import TwoAxisHelicoid.HelicoidProjectionBound

namespace TwoAxisHelicoid
open Set Filter Bornology
open scoped Topology

/-- Once the global graph has been constructed, arbitrary spatially thin
tails imply decay of its actual height in the base coordinates. The escape
of the inverse graph from every compact subset is derived from the actual
normal-coordinate estimate. -/
theorem helicoid_graph_height_decay {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (hX : Continuous X)
    {B : Set (ℝ × ℝ)} {Y : B → M} {u : B → ℝ} {r : ℝ} (hr : r < 1)
    (hu : ∀ b, |u b| ≤ r)
    (hgraph : ∀ b, X (Y b) = helicoidTubeMap ((u b,b.1.1),b.1.2))
    (hthin : ∀ ε : ℝ, 0 < ε → ∃ K : Set M, IsCompact K ∧
      ∀ q ∉ K, |helicoidSignedDistance (X q)| < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ b : B, T < ‖b.1‖ → |u b| < ε := by
  intro ε hε
  obtain ⟨K,hK,hsmall⟩ := hthin ε hε
  obtain ⟨C,hC0,hC⟩ := (hK.image hX).isBounded.exists_pos_norm_le
  refine ⟨2*C+2,by positivity,?_⟩
  intro b hb
  have hstrip : ((u b,b.1.1),b.1.2) ∈ helicoidTubeStrip := (hu b).trans_lt hr
  have hd : helicoidSignedDistance (X (Y b)) = u b := by
    rw [hgraph b]
    exact helicoidSignedDistance_on_normal hstrip
  have hnot : Y b ∉ K := by
    intro hk
    have hc := hC (X (Y b)) ⟨Y b,hk,rfl⟩
    have hbound := helicoid_normal_parameters_norm_bound b.1.1 b.1.2 (u b) ((hu b).trans hr.le)
    rw [← hgraph b] at hbound
    change ‖b.1‖ ≤ 2*‖X (Y b)‖+1 at hbound
    linarith
  simpa only [hd] using hsmall (Y b) hnot

theorem helicoid_graph_height_tendsto_zero {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (hX : Continuous X)
    {B : Set (ℝ × ℝ)} {Y : B → M} {u : B → ℝ} {r : ℝ} (hr : r < 1)
    (hu : ∀ b, |u b| ≤ r)
    (hgraph : ∀ b, X (Y b) = helicoidTubeMap ((u b,b.1.1),b.1.2))
    (hthin : ∀ ε : ℝ, 0 < ε → ∃ K : Set M, IsCompact K ∧
      ∀ q ∉ K, |helicoidSignedDistance (X q)| < ε) :
    Tendsto u (Filter.comap (Subtype.val : B → ℝ × ℝ) (cobounded (ℝ × ℝ))) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨T,_hT,hbound⟩ := helicoid_graph_height_decay hX hr hu hgraph hthin ε hε
  have he : ∀ᶠ z : ℝ × ℝ in cobounded (ℝ × ℝ), T < ‖z‖ :=
    tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop T)
  apply Filter.mem_comap.mpr
  refine ⟨{z : ℝ × ℝ | T < ‖z‖},he,?_⟩
  intro b hb
  change dist (u b) 0 < ε
  simpa only [dist_zero_right,Real.norm_eq_abs] using hbound b hb

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoid_graph_height_tendsto_zero
