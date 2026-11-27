import TwoAxisHelicoid.ComplexEndOnePointCharts

namespace TwoAxisHelicoid
open Complex Set Filter Topology Metric
open scoped Topology OnePoint

/-- Restrict a coordinate about the added point to its punctured disk on
the original space. Compactness of the complementary core and both end
limits follow from the topology of the one-point compactification. -/
theorem compact_point_chart_gives_punctured_end {M : Type*} [TopologicalSpace M] [T2Space M]
    (b : M)
    (χ : OpenPartialHomeomorph (OnePoint M) ℂ) (hp : ∞ ∈ χ.source) (h0 : χ ∞ = 0) :
    ∃ E : PuncturedComplexEnd M, (∀ x : M, E.coord x = χ (x:OnePoint M)) ∧
      (∀ x ∈ E.coord.source, (x:OnePoint M) ∈ χ.source) ∧
      (∀ w ∈ E.coord.target, (E.coord.symm w : OnePoint M) = χ.symm w) := by
  have hzero : (0:ℂ) ∈ χ.target := h0 ▸ χ.map_source hp
  obtain ⟨r,hr,hB⟩ := Metric.mem_nhds_iff.mp (χ.open_target.mem_nhds hzero)
  let U := χ.source ∩ χ ⁻¹' ball (0:ℂ) r
  have hU : IsOpen U := χ.isOpen_inter_preimage isOpen_ball
  have hUinf : ∞ ∈ U := ⟨hp,by change χ ∞ ∈ ball 0 r; rw [h0]; exact mem_ball_self hr⟩
  have hnon (w : ℂ) (hw : w ∈ ball (0:ℂ) r \ {0}) : χ.symm w ≠ ∞ := by
    intro h
    exact hw.2 ((χ.right_inv (hB hw.1)).symm.trans ((congrArg χ h).trans h0))
  let g := fun w : ℂ => (χ.symm w).elim b id
  have hge {w : ℂ} (hw : w ∈ ball (0:ℂ) r \ {0}) : (g w : OnePoint M) = χ.symm w := by
    obtain ⟨x,hx⟩ := OnePoint.ne_infty_iff_exists.mp (hnon w hw)
    change (((χ.symm w).elim b id : M) : OnePoint M) = χ.symm w
    rw [← hx]
    rfl
  let e : OpenPartialHomeomorph M ℂ :=
    { toFun := fun x => χ (x:OnePoint M)
      invFun := g
      source := OnePoint.some ⁻¹' U
      target := ball (0:ℂ) r \ {0}
      map_source' := fun x hx => ⟨hx.2,fun h => OnePoint.coe_ne_infty x (χ.injOn hx.1 hp (h.trans h0.symm))⟩
      map_target' := fun w hw => by
        change (g w:OnePoint M) ∈ U
        rw [hge hw]
        exact ⟨χ.map_target (hB hw.1),by change χ (χ.symm w) ∈ ball 0 r; rw [χ.right_inv (hB hw.1)]; exact hw.1⟩
      left_inv' := fun x hx => by
        change (χ.symm (χ (x:OnePoint M))).elim b id = x
        rw [χ.left_inv hx.1]
        rfl
      right_inv' := fun w hw => by
        rw [hge hw,χ.right_inv (hB hw.1)]
      open_source := hU.preimage OnePoint.continuous_coe
      open_target := isOpen_ball.sdiff isClosed_singleton
      continuousOn_toFun := fun _ hx => ((χ.continuousAt hx.1).comp OnePoint.continuous_coe.continuousAt).continuousWithinAt
      continuousOn_invFun := fun w hw => by
        obtain ⟨x,hx⟩ := OnePoint.ne_infty_iff_exists.mp (hnon w hw)
        have he : ContinuousAt (fun q : OnePoint M => q.elim b id) (χ.symm w) := hx ▸ OnePoint.continuousAt_coe.mpr continuousAt_id
        exact (he.comp (χ.symm.continuousAt (hB hw.1))).continuousWithinAt }
  have hcc : IsCompact e.sourceᶜ := ((OnePoint.isOpen_iff_of_mem' hUinf).mp hU).1
  have hinfty : Tendsto (OnePoint.some : M → OnePoint M) (cocompact M) (𝓝 ∞) :=
    Filter.coclosedCompact_eq_cocompact (X := M) ▸ OnePoint.tendsto_coe_infty
  have hto : Tendsto e (cocompact M) (𝓝 0) := h0 ▸ (χ.continuousAt hp).tendsto.comp hinfty
  have hχ0 : χ.symm 0 = ∞ := h0 ▸ χ.left_inv hp
  have hfrom : Tendsto e.symm (𝓝[≠] (0:ℂ)) (cocompact M) := by
    rw [← Filter.coclosedCompact_eq_cocompact (X := M),← OnePoint.comap_coe_nhds_infty,tendsto_comap_iff]
    have hlim : Tendsto χ.symm (𝓝[≠] (0:ℂ)) (𝓝 ∞) :=
      hχ0 ▸ (χ.symm.continuousAt hzero).tendsto.mono_left nhdsWithin_le_nhds
    apply hlim.congr'
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0:ℂ) hr),self_mem_nhdsWithin] with w hw hn
    exact (hge ⟨hw,hn⟩).symm
  exact ⟨⟨e,r,hr,rfl,hcc,hto,hfrom⟩,fun _ => rfl,fun _ hx => hx.1,fun _ hw => hge hw⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_point_chart_gives_punctured_end
