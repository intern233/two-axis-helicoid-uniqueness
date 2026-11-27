import TwoAxisHelicoid.PlaneTranslationLattice
import TwoAxisHelicoid.PointedTorusUniformization

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff Manifold

/-- A holomorphic covering of a compact Hausdorff Riemann surface by the
ordinary complex plane yields its actual complex torus uniformization.
The covering periods, their two-generator lattice, and the biholomorphism
are all constructed. -/
theorem compact_surface_uniformizes_of_holomorphic_plane_cover
    {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace ℂ M]
    {p : ℂ → M} (hp : HolomorphicPlaneCover p) : AdmitsPeriodTorusUniformization M := by
  obtain ⟨L,hL⟩ := compact_plane_cover_periodPair hp
  have hper (z v : ℂ) (hv : v ∈ L.lattice) : p (z+v) = p z := by
    have h : v ∈ L.lattice.toAddSubgroup := hv
    rw [hL] at h
    exact h z
  let φ := periodTorusLift L p hper
  have hπ (z : ℂ) : φ (periodTorusProjection L z) = p z := rfl
  have hc : Continuous φ := QuotientAddGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff.mpr hp.covering.continuous
  have hj : Function.Injective φ := by
    intro x y hh
    obtain ⟨u,rfl⟩ := (Quotient.mk_surjective : Function.Surjective (periodTorusProjection L)) x
    obtain ⟨v,rfl⟩ := (Quotient.mk_surjective : Function.Surjective (periodTorusProjection L)) y
    apply (periodTorusProjection_eq_iff L u v).mpr
    change v-u ∈ L.lattice.toAddSubgroup
    rw [hL]
    exact (planeCoverPeriods_fiber_eq hp u v).mp hh
  have hs : Function.Surjective φ := fun x => by
    obtain ⟨z,hz⟩ := hp.onto x
    exact ⟨periodTorusProjection L z,hz⟩
  let e := Equiv.ofBijective φ ⟨hj,hs⟩
  let H := (show Continuous e from hc).homeoOfEquivCompactToT2
  have hH (z : ℂ) : H (periodTorusProjection L z) = p z := rfl
  have hf : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H := by
    intro q
    let c := chartAt ℂ q
    have ha := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℂ,ℂ)) (n := ω)
      (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ q)) (mem_chart_source ℂ q)
    apply (hp.contMDiff.contMDiffAt.comp q ha).congr_of_eventuallyEq
    filter_upwards [c.open_source.mem_nhds (mem_chart_source ℂ q)] with y hy
    change H y = p (c y)
    rw [← hH,← periodTorus_chart_symm_eq_projection L q]
    exact congrArg H (c.left_inv hy).symm
  have hi : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm := by
    intro x
    obtain ⟨z,rfl⟩ := hp.onto x
    obtain ⟨c,hc',hz,he⟩ := hp.local_chart z
    have hx : p z ∈ c.source := he.self_of_nhds ▸ c.map_target hz
    have hcz : c (p z) = z := he.self_of_nhds ▸ c.right_inv hz
    have hd := (periodTorusProjection_contMDiff L).contMDiffAt.comp (p z) (contMDiffAt_of_mem_maximalAtlas hc' hx)
    apply hd.congr_of_eventuallyEq
    have hn : ∀ᶠ w in 𝓝 (c (p z)), c.symm w = p w := hcz.symm ▸ he
    filter_upwards [c.open_source.mem_nhds hx,(c.continuousAt hx).eventually hn] with q hq hh
    change H.symm q = periodTorusProjection L (c q)
    apply H.injective
    rw [H.apply_symm_apply,hH,← hh,c.left_inv hq]
  exact ⟨L,H.symm,hi,hf⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_surface_uniformizes_of_holomorphic_plane_cover
