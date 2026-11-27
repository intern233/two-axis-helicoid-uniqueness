import TwoAxisHelicoid.ChartPunctureDiskHomeomorphism

namespace TwoAxisHelicoid
open Set Metric Topology

/-- The complement of any compact set contained in one open plane chart
contains an open copy of the surface punctured at the chart origin. -/
theorem punctured_surface_embeds_outside_compact_planar_chart {M : Type*}
    [TopologicalSpace M] [T2Space M] (j : ℂ → M) (openj : IsOpenEmbedding j)
    (K : Set M) (compact : IsCompact K) (inside : K⊆range j) :
    ∃ f : {x : M // x≠j 0} → {x : M // x∉K}, IsOpenEmbedding f := by
  let e := (openj.toOpenPartialHomeomorph j).symm
  have src : e.source=range j := openj.toOpenPartialHomeomorph_target j
  have tgt : e.target=univ := openj.toOpenPartialHomeomorph_source j
  have hp : j 0∈e.source := by rw [src]; exact mem_range_self 0
  have center : e (j 0)=0 := openj.toOpenPartialHomeomorph_left_inv j
  have ck : IsCompact (j ⁻¹' K) := openj.isEmbedding.isCompact_iff.mpr (by rwa [image_preimage_eq_of_subset inside])
  obtain ⟨R,hr⟩ := ck.isBounded.exists_norm_le
  let r := max R 1
  have pos : 0<r := one_pos.trans_le (le_max_right R 1)
  have all (s : ℝ) : closedBall (e (j 0)) s⊆e.target := by rw [tgt]; exact subset_univ _
  let C := e.symm '' closedBall (e (j 0)) r
  have contains : K⊆C := by
    intro x hx
    obtain ⟨z,rfl⟩ := inside hx
    refine ⟨z,?_,rfl⟩
    rw [center,mem_closedBall,dist_zero_right]
    exact (hr z hx).trans (le_max_left R 1)
  have closed : IsClosed C := ((isCompact_closedBall _ _).image_of_continuousOn
    (e.continuousOn_symm.mono (all r))).isClosed
  obtain ⟨puncture⟩ := chart_puncture_closed_disk_homeomorphism e hp pos (all (2*r))
  let incl : Cᶜ⊆Kᶜ := fun _ hx hk => hx (contains hk)
  refine ⟨inclusion incl ∘ puncture,?_⟩
  exact (Topology.IsOpenEmbedding.inclusion incl (closed.isOpen_compl.preimage continuous_subtype_val)).comp puncture.isOpenEmbedding

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.punctured_surface_embeds_outside_compact_planar_chart
