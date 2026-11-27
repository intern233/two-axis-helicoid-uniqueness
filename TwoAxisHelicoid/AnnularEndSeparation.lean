import TwoAxisHelicoid.ExteriorHeightEscape
import TwoAxisHelicoid.AnnularEndInverseEscape

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology

/-- A one-ended surface eventually lies on just one side of any compact
coordinate circle contained in an end chart. -/
theorem end_chart_eventually_one_side {M : Type*} [TopologicalSpace M] (tails : HasConnectedCompactTails M)
    (e : OpenPartialHomeomorph M ℂ) (core : IsCompact e.sourceᶜ) (s : ℝ) (circle : sphere (0:ℂ) s⊆e.target) :
    (∀ᶠ x in cocompact M, ‖e x‖<s) ∨ (∀ᶠ x in cocompact M, s<‖e x‖) := by
  let K := e.symm '' sphere (0:ℂ) s
  have compact : IsCompact K := (isCompact_sphere _ _).image_of_continuousOn (e.continuousOn_invFun.mono circle)
  obtain ⟨U,conn,k,dis⟩ := tails _ (core.union compact)
  have src (x : M) (hx : x∈U) : x∈e.source := by
    by_contra out
    exact disjoint_left.mp dis hx (Or.inl out)
  have no (x : M) (hx : x∈U) : ‖e x‖≠s := by
    intro eq
    exact disjoint_left.mp dis hx (Or.inr ⟨e x,by simpa only [mem_sphere,dist_zero_right] using eq,e.left_inv (src x hx)⟩)
  let T := (fun x => ‖e x‖) '' U
  have cT : IsPreconnected T := conn.image _ ((e.continuousOn.mono (fun x h => src x h)).norm)
  have sT : T⊆Iio s∪Ioi s := by
    rintro _ ⟨x,h,rfl⟩
    exact lt_or_gt_of_ne (no x h)
  have ev : ∀ᶠ x in cocompact M, x∈U := by
    change U∈cocompact M
    simpa only [compl_compl] using k.compl_mem_cocompact
  rcases cT.subset_or_subset isOpen_Iio isOpen_Ioi (disjoint_left.mpr fun _ a b => (a : _<s).asymm b) sT with lo|hi
  · exact Or.inl (ev.mono fun _ hx => lo (mem_image_of_mem _ hx))
  · exact Or.inr (ev.mono fun _ hx => hi (mem_image_of_mem _ hx))

/-- A compact closed radial band inside the chart is left behind by
all points escaping through the surface end. -/
theorem end_chart_avoids_compact_band {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M ℂ) (core : IsCompact e.sourceᶜ) (a b : ℝ)
    (band : {z : ℂ | a≤‖z‖ ∧ ‖z‖≤b}⊆e.target) :
    ∀ᶠ x in cocompact M, ¬(a≤‖e x‖ ∧ ‖e x‖≤b) := by
  let S := {z : ℂ | a≤‖z‖ ∧ ‖z‖≤b}
  have cs : IsCompact S := (isCompact_closedBall (0:ℂ) b).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
    (fun z hz => by simpa only [mem_closedBall,dist_zero_right] using hz.2)
  have cc := cs.image_of_continuousOn (e.continuousOn_invFun.mono band)
  have src : e.source∈cocompact M := by simpa only [compl_compl] using core.compl_mem_cocompact
  filter_upwards [src,cc.compl_mem_cocompact] with x hx out h
  exact out ⟨e x,h,e.left_inv hx⟩

theorem end_chart_reaches_lower_radius {M : Type*} [TopologicalSpace M] (e : OpenPartialHomeomorph M ℂ)
    (core : IsCompact e.sourceᶜ) {r m : ℝ} (_rm : r<m)
    (round : ∀ z : ℂ, ‖z‖≤m → (z∈e.target ↔ r<‖z‖))
    (side : ∀ᶠ x in cocompact M, ‖e x‖<m) :
    Tendsto (fun x => ‖e x‖) (cocompact M) (𝓝 r) := by
  have src : e.source∈cocompact M := by simpa only [compl_compl] using core.compl_mem_cocompact
  apply tendsto_order.mpr
  constructor
  · intro a ar
    filter_upwards [src,side] with x hx small
    exact ar.trans ((round _ small.le).mp (e.map_source hx))
  · intro b rb
    by_cases bm : b<m
    · have outside := end_chart_avoids_compact_band e core b m (fun z hz => (round z hz.2).mpr (rb.trans_le hz.1))
      filter_upwards [outside,side] with x no sm using lt_of_not_ge (fun ge => no ⟨ge,sm.le⟩)
    · exact side.mono fun _ h => h.trans_le (le_of_not_gt bm)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.end_chart_reaches_lower_radius
